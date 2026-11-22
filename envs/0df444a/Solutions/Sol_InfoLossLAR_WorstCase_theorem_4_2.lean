-- Prove2me | solution 1 for InfoLossLAR.WorstCase.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T23:31:30.833923+00:00
-- url     : https://prove2.me/submissions/d72f2765-538a-4dbe-9c4c-fcb4f4196405

import Theorems.Thm_InfoLossLAR_WorstCase_lemma_3_5
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_02
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_05
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_06_Optimized
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_07
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_08
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_09
import Definitions.Def_InfoLossLAR_LoadedBatchBundle_01
import Definitions.Def_InfoLossLAR_NativeSparsePrefix_02
import Definitions.Def_InfoLossLAR_Native_AFT_FiniteProbability
import Definitions.Def_InfoLossLAR_Native_AFT_Histogram
import Definitions.Def_InfoLossLAR_Native_AFT_Hoeffding
import Definitions.Def_InfoLossLAR_RuntimeBundle_01
import Definitions.Def_InfoLossLAR_RuntimeBundle_02
import Definitions.Def_InfoLossLAR_RuntimeBundle_03
import Definitions.Def_InfoLossLAR_WorstCase_Encoding
import Definitions.Def_InfoLossLAR_WorstCase_Family
import Definitions.Def_InfoLossLAR_WorstCase_FixedT
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_InfoLossLAR_WorstCase_Rounding
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalStringListEncoding
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Mathlib
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Vector.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Order.Hom.Set
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic

set_option linter.all false

namespace AFT
end AFT

namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic

namespace AFT.GaussianSource
end AFT.GaussianSource

namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial

namespace AFT.SafeConvolution
end AFT.SafeConvolution

namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase.TM2Boolean
end InfoLossLAR.WorstCase.TM2Boolean

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN
end InfoLossLAR.WorstCase.TM2Boolean.RPN

namespace Integration9_9
end Integration9_9

namespace Integration9_9.LARCoinLayout
end Integration9_9.LARCoinLayout

namespace Integration9_9.LARCoinMachine
end Integration9_9.LARCoinMachine

namespace Integration9_9.LARPlatformEncoding
end Integration9_9.LARPlatformEncoding

namespace Integration9_9.LARRankOneMachine
end Integration9_9.LARRankOneMachine

namespace Integration9_9.TM2OutputLength
end Integration9_9.TM2OutputLength

namespace Integration9_9.TM2PlatformSerialization
end Integration9_9.TM2PlatformSerialization

namespace Integration9_9.TM2PolynomialBudget
end Integration9_9.TM2PolynomialBudget

namespace Integration9_9.TM2StockLists
end Integration9_9.TM2StockLists

namespace OAI.MetricKMedian.Binary
end OAI.MetricKMedian.Binary

namespace OAI.MetricKMedian.Binary.Automatic
end OAI.MetricKMedian.Binary.Automatic

namespace OAI.MetricKMedian.Binary.Automatic.Poly
end OAI.MetricKMedian.Binary.Automatic.Poly

namespace QMCNumericRuntime
end QMCNumericRuntime

/- Helper module AFT.FiniteProbability. -/
section P2MDyadicModule0

namespace AFT

namespace FiniteDist

open scoped Classical

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- Keep an arbitrary fixed side value while permuting an input. -/
theorem map_equiv_pair_weight (p : FiniteDist α) (e : α ≃ β)
    (c : γ) (b : β) (d : γ) :
    (p.map (fun a => (e a, c))).weight (b, d) =
      if c = d then p.weight (e.symm b) else 0 := by
  by_cases h : c = d
  · subst d
    simp [map_weight, e.apply_eq_iff_eq_symm_apply]
  · simp [map_weight, Prod.mk.injEq, h]

/-- The transformed uniform input is independent of any side information
computed from the sampler randomness. The sampler's internal coordinates may
be arbitrarily correlated. This is equality of the entire joint law. -/
theorem random_equiv_independent [Nonempty β] (p : FiniteDist α)
    (e : α → β ≃ β) (side : α → γ) :
    p.mix (fun a => (uniform β).map (fun b => (e a b, side a))) =
      (uniform β).prod (p.map side) := by
  ext bc
  rcases bc with ⟨b, c⟩
  simp only [mix_weight, map_equiv_pair_weight, prod_weight, uniform_weight]
  rw [map_weight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : side a = c <;> simp [h, mul_comm]

end FiniteDist

end AFT

end P2MDyadicModule0

/- Helper module AFT.JointPairOutput. -/
section P2MDyadicModule1

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem prod_map_functions (first : FiniteDist A) (second : FiniteDist B) (f : A → C) (g : B → D) :
    (first.prod second).map (fun pair => (f pair.1, g pair.2)) = (first.map f).prod (second.map g) := by
  apply FiniteDist.ext
  rintro ⟨c, d⟩
  simp only [map_weight, prod_weight, Fintype.sum_prod_type, Prod.mk.injEq,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp_all

end

end AFT.FiniteDist

namespace AFT.SafeConvolution

open scoped BigOperators Classical

noncomputable section

variable {G : Type*} [Fintype G] [AddCommGroup G]

end

end AFT.SafeConvolution

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Color : Type*} [Fintype Color]

attribute [local instance] AFT.RepresentedPolynomial.jointPairFinDecEq

end

end AFT.RepresentedPolynomial

namespace AFT.GaussianSource

noncomputable section

end

end AFT.GaussianSource

namespace AFT.V7Calibration

open GaussianSource SafeConvolution RepresentedPolynomial Filter

open scoped BigOperators Classical Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false

end

end AFT.V7Calibration

end P2MDyadicModule1

/- Helper module Solutions.AdvantageBridgeQuantumProbability. -/
section P2MDyadicModule2

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

/-- The quantum acceptance tests used in the statistical hybrids are bounded
between zero and one for every family in the published gate model. -/
theorem acceptProb_mem_unitInterval (D : Family) (w : Str) :
    0 ≤ acceptProb D w ∧ acceptProb D w ≤ 1 := by
  have hmass : (∑ y : Bits (w.length + (D.anc w.length + 1)),
      ‖runLayered (D.circ w.length) (basisInput (toBits w)) y‖ ^ 2) = 1 := by
    simpa only [Complex.normSq_eq_norm_sq] using
      (runLayered_mass (D.circ w.length) (basisInput (toBits w))).trans
        (basisInput_mass (a := D.anc w.length) (toBits w))
  unfold acceptProb
  constructor
  · apply Finset.sum_nonneg
    intro y hy
    split_ifs <;> positivity
  · calc
      _ ≤ ∑ y : Bits (w.length + (D.anc w.length + 1)),
        ‖runLayered (D.circ w.length) (basisInput (toBits w)) y‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro y hy
          split_ifs <;> first | exact le_rfl | positivity
      _ = 1 := hmass

end InfoLossLAR.WorstCase

end P2MDyadicModule2

/- Helper module Solutions.AdvantageBridgeLWEHybrid. -/
section P2MDyadicModule3

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

/-- Averaging a uniformly bounded pointwise difference preserves its bound. -/
theorem avg_abs_sub_le {α : Type*} [Fintype α] [Nonempty α]
    (f g : α → ℝ) (error : ℝ) (herror : ∀ x, |f x - g x| ≤ error) :
    |avg f - avg g| ≤ error := by
  have hcard : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : |(∑ x, f x) - ∑ x, g x| ≤ (Fintype.card α : ℝ) * error := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ x, (f x - g x)| ≤ ∑ x, |f x - g x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : α, error := Finset.sum_le_sum (fun x hx => herror x)
      _ = _ := by simp
  unfold avg
  rw [← sub_div, abs_div, abs_of_nonneg hcard.le]
  exact (div_le_iff₀ hcard).mpr (by simpa [mul_comm] using hsum)

end InfoLossLAR.WorstCase

end P2MDyadicModule3

/- Helper module Solutions.AdvantageBridgeLARZeroSecret. -/
section P2MDyadicModule4

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped Classical

/-- A finite uniform average of actual probabilities is an actual probability. -/
theorem avg_mem_unitInterval {α : Type*} [Fintype α] [Nonempty α]
    (test : α → ℝ) (htest : ∀ x, 0 ≤ test x ∧ test x ≤ 1) :
    0 ≤ avg test ∧ avg test ≤ 1 := by
  have hc : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun x _ => (htest x).1) hc.le
  · apply (div_le_one hc).mpr
    calc
      ∑ x, test x ≤ ∑ _ : α, (1 : ℝ) := Finset.sum_le_sum fun x _ => (htest x).2
      _ = _ := by simp

/-- Changing a uniform finite experiment at one point has exactly its point mass cost. -/
theorem avg_replace_point_abs {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    (test : α → ℝ) (point : α) (replacement : ℝ) :
    |avg test - avg (fun x => if x = point then replacement else test x)| =
      (Fintype.card α : ℝ)⁻¹ * |test point - replacement| := by
  have hc : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hd (x : α) : test x - (if x = point then replacement else test x) =
      if x = point then test point - replacement else 0 := by
    by_cases h : x = point <;> simp [h]
  unfold avg
  rw [← sub_div, ← Finset.sum_sub_distrib]
  simp_rw [hd]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [abs_div, abs_of_pos hc]
  simp only [div_eq_mul_inv, mul_comm]

/-- The real platform experiment and its zero-secret replacement differ by
exactly the uniform secret's zero mass times the conditional acceptance gap. -/
theorem prRealLAR_zeroSecretReplacement_exact (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) :
    |prRealLAR D lam pp q N d ℓ t label -
      prZeroSecretReplacedLAR D lam pp q N d ℓ t label| =
      ((q : ℝ)^N)⁻¹ * |larSecretAcceptance D lam pp q N d ℓ t label 0 -
        prIdealLAR D lam pp q N d ℓ t| := by
  have h := avg_replace_point_abs (larSecretAcceptance D lam pp q N d ℓ t label)
    0 (prIdealLAR D lam pp q N d ℓ t)
  unfold larSecretAcceptance at h
  simpa only [prRealLAR, prZeroSecretReplacedLAR, larSecretAcceptance,
    Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow] using h

end InfoLossLAR.WorstCase

end P2MDyadicModule4

/- Helper module Solutions.AdvantageBridgeAlignment. -/
section P2MDyadicModule5

set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace InfoLossLAR.WorstCase

open Matrix

open scoped BigOperators Classical

private theorem alignment_avg_const {α : Type*} [Fintype α] [Nonempty α] (value : ℝ) :
    avg (fun _ : α => value) = value := by
  simp [avg,Fintype.card_ne_zero]

private theorem alignment_avg_add {α : Type*} [Fintype α] (first second : α → ℝ) :
    avg (fun x => first x+second x) = avg first+avg second := by
  simp only [avg,Finset.sum_add_distrib,add_div]

private theorem alignment_avg_mul {α : Type*} [Fintype α] (constant : ℝ) (test : α → ℝ) :
    avg (fun x => constant*test x) = constant*avg test := by
  simp only [avg,←Finset.mul_sum]
  ring

private theorem alignment_avg_mul_right {α : Type*} [Fintype α] (test : α → ℝ) (constant : ℝ) :
    avg (fun x => test x*constant) = avg test*constant := by
  simp only [avg,←Finset.sum_mul]
  ring

private theorem alignment_avg_comm {α β : Type*} [Fintype α] [Fintype β] (test : α → β → ℝ) :
    avg (fun a => avg (fun b => test a b)) = avg (fun b => avg (fun a => test a b)) := by
  simp only [avg,←Finset.sum_div]
  rw [Finset.sum_comm]
  ring

private theorem alignment_avg_translate {α : Type*} [AddGroup α] [Fintype α]
    (shift : α) (test : α → ℝ) : avg (fun x => test (x+shift)) = avg test := by
  unfold avg
  exact congrArg (fun value : ℝ => value/(Fintype.card α : ℝ)) (Equiv.sum_comp (Equiv.addRight shift) test)

/-- A nonzero finite-field linear functional sends the actual uniform vector to uniform scalars. -/
theorem avg_dotProduct_nonzero {F : Type*} [Field F] [Fintype F] {N : ℕ}
    (secret : Fin N → F) (hsecret : secret ≠ 0) (test : F → ℝ) :
    avg (fun auxiliary : Fin N → F => test (auxiliary ⬝ᵥ secret)) = avg test := by
  have hex : ∃ index, secret index ≠ 0 := by
    by_contra h
    push_neg at h
    exact hsecret (funext h)
  obtain ⟨index,hindex⟩ := hex
  let direction : Fin N → F := Pi.single index ((secret index)⁻¹)
  have hdirection : direction ⬝ᵥ secret = 1 := by
    simp only [direction,single_dotProduct]
    exact inv_mul_cancel₀ hindex
  have htranslate (scalar : F) :
      avg (fun auxiliary : Fin N → F => test (auxiliary ⬝ᵥ secret+scalar)) =
        avg (fun auxiliary : Fin N → F => test (auxiliary ⬝ᵥ secret)) := by
    simpa only [add_dotProduct,smul_dotProduct,hdirection,smul_eq_mul,mul_one] using
      alignment_avg_translate (scalar • direction) (fun auxiliary => test (auxiliary ⬝ᵥ secret))
  calc
    _ = avg (fun scalar : F => avg (fun auxiliary : Fin N → F =>
        test (auxiliary ⬝ᵥ secret+scalar))) := by
      simp_rw [htranslate]
      rw [alignment_avg_const]
    _ = avg (fun auxiliary : Fin N → F => avg (fun scalar : F =>
        test (auxiliary ⬝ᵥ secret+scalar))) := alignment_avg_comm _
    _ = avg (fun _ : Fin N → F => avg test) := by
      congr 1
      funext auxiliary
      simpa only [add_comm] using alignment_avg_translate (auxiliary ⬝ᵥ secret) test
    _ = _ := alignment_avg_const _

private theorem alignment_avg_ite {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    (point : α) (real ideal : ℝ) :
    avg (fun x : α => if x=point then real else ideal) =
      (1/(Fintype.card α : ℝ))*real+(1-1/(Fintype.card α : ℝ))*ideal := by
  have hpoint : avg (fun x : α => if x=point then (1 : ℝ) else 0) = 1/(Fintype.card α : ℝ) := by
    simp [avg]
  have hfun : (fun x : α => if x=point then real else ideal) =
      (fun x => (if x=point then (1 : ℝ) else 0)*(real-ideal)+ideal) := by
    funext x
    by_cases h : x=point <;> simp [h]
  rw [hfun,alignment_avg_add,alignment_avg_mul_right,alignment_avg_const,hpoint]
  ring

open QAlgorithms.Complexity

/-- The complete actual Game 2 acceptance is its exact mixture of Game 1 and ideal LAR. -/
theorem prAlignmentLAR_eq_mixture (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) :
    prAlignmentLAR D lam pp q N d ℓ t label =
      (1/(q : ℝ))*prZeroSecretReplacedLAR D lam pp q N d ℓ t label+
        (1-1/(q : ℝ))*prIdealLAR D lam pp q N d ℓ t := by
  let ideal := prIdealLAR D lam pp q N d ℓ t
  let real := larSecretAcceptance D lam pp q N d ℓ t label
  have hview (secret auxiliary : Fin N → ZMod q) :
      (avg fun matrices : Fin t → Matrix (Fin d) (Fin N) (ZMod q) =>
        if auxiliary ⬝ᵥ secret=1 then
          acceptProb D (encInput lam pp (encTable
            (fun i => (matrices i,label ((matrices i).mulVec secret)))))
        else avg fun labels : Fin t → Fin ℓ → ZMod q =>
          acceptProb D (encInput lam pp (encTable (fun i => (matrices i,labels i))))) =
        if auxiliary ⬝ᵥ secret=1 then real secret else ideal := by
    by_cases h : auxiliary ⬝ᵥ secret=1
    · simp only [if_pos h]
      rfl
    · simp only [if_neg h]
      rfl
  have hsecret (secret : Fin N → ZMod q) :
      (avg fun auxiliary : Fin N → ZMod q =>
        if auxiliary ⬝ᵥ secret=1 then real secret else ideal) =
      (1/(q : ℝ))*(if secret=0 then ideal else real secret)+(1-1/(q : ℝ))*ideal := by
    by_cases hs : secret=0
    · subst secret
      simp only [dotProduct_zero,zero_ne_one,if_false,if_true]
      rw [alignment_avg_const]
      ring
    · rw [avg_dotProduct_nonzero secret hs
        (fun scalar : ZMod q => if scalar=1 then real secret else ideal)]
      simpa only [ZMod.card,hs,if_false] using alignment_avg_ite (1 : ZMod q) (real secret) ideal
  unfold prAlignmentLAR
  simp_rw [hview,hsecret]
  rw [alignment_avg_add,alignment_avg_mul,alignment_avg_const]
  rfl

/-- Exact `q` scaling between the two genuine LAR games and the ideal experiment. -/
theorem prAlignmentLAR_scaled (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) :
    (q : ℝ)*(prAlignmentLAR D lam pp q N d ℓ t label-prIdealLAR D lam pp q N d ℓ t) =
      prZeroSecretReplacedLAR D lam pp q N d ℓ t label-prIdealLAR D lam pp q N d ℓ t := by
  rw [prAlignmentLAR_eq_mixture]
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  field_simp [hq] <;> ring

/-- The exact advantage form of the genuine Game 1 to Game 2 identity. -/
theorem prAlignmentLAR_advantage_scaling (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) :
    |prZeroSecretReplacedLAR D lam pp q N d ℓ t label-prIdealLAR D lam pp q N d ℓ t| =
      (q : ℝ)*|prAlignmentLAR D lam pp q N d ℓ t label-prIdealLAR D lam pp q N d ℓ t| := by
  rw [←prAlignmentLAR_scaled D lam pp q N d ℓ t label,abs_mul,abs_of_nonneg (Nat.cast_nonneg q)]

end InfoLossLAR.WorstCase

end P2MDyadicModule5

/- Helper module Solutions.AdvantageBridgeRankOne. -/
section P2MDyadicModule6

set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace InfoLossLAR.WorstCase

open Matrix AFT

open scoped BigOperators Classical

/-- A fixed side input, with an arbitrary distribution, remains independent
of the public matrix in the nonaligned branch. -/
theorem rankOneMatrix_unaligned_joint {F Label : Type*} [Field F] [Fintype F]
    [Fintype Label] {d N : ℕ}
    (secret auxiliary : Fin N → F) (hmiss : auxiliary ⬝ᵥ secret ≠ 1)
    (source : FiniteDist (Fin d → F)) (label : (Fin d → F) → Label) :
    source.mix (fun input =>
      (FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).map
        (fun matrix => (rankOneMatrix secret auxiliary matrix input, label input))) =
      (FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).prod (source.map label) :=
  FiniteDist.random_equiv_independent source
    (fun input => rankOneUnalignedEquiv secret auxiliary hmiss input) label

private theorem uniform_pair_eq_product {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] :
    FiniteDist.uniform (α × β) = (FiniteDist.uniform α).prod (FiniteDist.uniform β) := by
  ext point
  simp only [FiniteDist.uniform_weight, FiniteDist.prod_weight,
    Fintype.card_prod, Nat.cast_mul, _root_.mul_inv_rev]
  ring

private theorem finite_prod_map_fst {α β : Type*} [Fintype α] [Fintype β]
    (first : FiniteDist α) (second : FiniteDist β) :
    (first.prod second).map Prod.fst = first := by
  ext point
  simp only [FiniteDist.map_weight, Fintype.sum_prod_type, FiniteDist.prod_weight]
  simp_rw [Finset.sum_ite_irrel, ← Finset.mul_sum, second.sum_one, mul_one]
  simp

/-- The aligned branch has the complete real-label law. This includes the
correlation between the output matrix and its label, not only uniform marginals. -/
theorem rankOneMatrix_aligned_joint {F Label : Type*} [CommRing F] [Fintype F]
    [Fintype Label] {d N : ℕ}
    (secret auxiliary : Fin N → F) (halign : auxiliary ⬝ᵥ secret = 1)
    (label : (Fin d → F) → Label) :
    (FiniteDist.uniform (Matrix (Fin d) (Fin N) F × (Fin d → F))).map
      (fun pair => (rankOneMatrix secret auxiliary pair.1 pair.2, label pair.2)) =
      (FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).map
        (fun matrix => (matrix, label (matrix.mulVec secret))) := by
  let transform := rankOneAlignedEquiv (d := d) secret auxiliary halign
  let observe := fun pair : Matrix (Fin d) (Fin N) F × (Fin d → F) =>
    (pair.1, label (pair.1.mulVec secret))
  have h := congrArg (fun law => law.map observe) (FiniteDist.uniform_map_equiv transform)
  rw [FiniteDist.map_map] at h
  have hs : (fun pair => observe (transform pair)) =
      (fun pair => (rankOneMatrix secret auxiliary pair.1 pair.2, label pair.2)) := by
    funext pair
    change (rankOneMatrix secret auxiliary pair.1 pair.2,
      label ((rankOneMatrix secret auxiliary pair.1 pair.2).mulVec secret)) = _
    rw [rankOneMatrix_aligned secret auxiliary halign]
  rw [hs] at h
  rw [h, uniform_pair_eq_product]
  let matrixLaw := FiniteDist.uniform (Matrix (Fin d) (Fin N) F)
  let hidden := FiniteDist.uniform (Fin d → F)
  let output := fun matrix : Matrix (Fin d) (Fin N) F =>
    (matrix, label (matrix.mulVec secret))
  have hm := FiniteDist.map_map (matrixLaw.prod hidden)
    (Prod.fst : Matrix (Fin d) (Fin N) F × (Fin d → F) → Matrix (Fin d) (Fin N) F) output
  exact hm.symm.trans (congrArg (fun law => law.map output) (finite_prod_map_fst matrixLaw hidden))

end InfoLossLAR.WorstCase

end P2MDyadicModule6

/- Helper module Integration9_9.ZeroFiber. -/
section P2MDyadicModule7

set_option autoImplicit false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.Integration

open AFT

/-- Uniform sampling of a nonempty predicate subtype is uniform on its finite support. -/
theorem uniform_subtype_weight {α : Type*} [Fintype α] [DecidableEq α]
    (P : α → Prop) [DecidablePred P] [Nonempty {x // P x}] (x : α) :
    ((FiniteDist.uniform {x // P x}).map Subtype.val).weight x =
      unifOn (Finset.univ.filter P) x := by
  classical
  rw [FiniteDist.map_weight]
  simp only [FiniteDist.uniform_weight]
  by_cases hx : P x
  · have heq (a : {x // P x}) : (a : α) = x ↔ a = ⟨x, hx⟩ := by
      simp only [Subtype.ext_iff]
    simp_rw [heq]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [unifOn, hx, Fintype.card_subtype]
  · have hne (a : {x // P x}) : (a : α) ≠ x := by
      intro h
      apply hx
      exact h ▸ a.property
    simp [hne, unifOn, hx]

end InfoLossLAR.WorstCase.Integration

end P2MDyadicModule7

/- Helper module Solutions.AdvantageBridgeZeroFiberDecomposition. -/
section P2MDyadicModule8

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

namespace InfoLossLAR.WorstCase

open AFT

open scoped BigOperators Classical

theorem zeroFiberCoordinates_label {V K : Type*} [AddCommGroup V] [AddCommGroup K]
    (label : V → K) (direction : K →+ V)
    (htranslate : ∀ x k, label (x + direction k) = label x + k)
    (pair : {x : V // label x = 0} × K) :
    label (zeroFiberCoordinates label direction htranslate pair) = pair.2 := by
  change label (pair.1.val + direction pair.2) = _
  rw [htranslate,pair.1.property,zero_add]

/-- Uniform error in the zero fiber plus an independent uniform label gives
an exactly uniform input, together with its correct label. -/
theorem zeroFiberCoordinates_uniform_joint {V K : Type*} [AddCommGroup V] [AddCommGroup K]
    [Fintype V] [Fintype K]
    (label : V → K) (direction : K →+ V)
    (htranslate : ∀ x k, label (x + direction k) = label x + k) :
    letI : Nonempty {x : V // label x = 0} :=
      ⟨⟨0 + direction (-label 0), by rw [htranslate]; simp⟩⟩
    ((FiniteDist.uniform {x : V // label x = 0}).prod (FiniteDist.uniform K)).map
      (fun pair => (pair.1.val + direction pair.2, pair.2)) =
      (FiniteDist.uniform V).map (fun x => (x, label x)) := by
  letI : Nonempty {x : V // label x = 0} :=
    ⟨⟨0 + direction (-label 0), by rw [htranslate]; simp⟩⟩
  have hp : (FiniteDist.uniform {x : V // label x = 0}).prod (FiniteDist.uniform K) =
      FiniteDist.uniform ({x : V // label x = 0} × K) := by
    ext pair
    simp only [FiniteDist.prod_weight,FiniteDist.uniform_weight,Fintype.card_prod,
      Nat.cast_mul,mul_inv_rev]
    ring
  rw [hp]
  let equiv := zeroFiberCoordinates label direction htranslate
  have hu := congrArg (fun law => law.map (fun x => (x,label x)))
    (FiniteDist.uniform_map_equiv equiv)
  rw [FiniteDist.map_map] at hu
  convert hu using 1
  apply congrArg
  funext pair
  change (pair.1.val + direction pair.2,pair.2) =
    (pair.1.val + direction pair.2,label (equiv pair))
  rw [zeroFiberCoordinates_label label direction htranslate pair]

private theorem zeroFiber_prod_map_snd {α β : Type*} [Fintype α] [Fintype β]
    (first : FiniteDist α) (second : FiniteDist β) :
    (first.prod second).map Prod.snd = second := by
  ext point
  simp only [FiniteDist.map_weight,Fintype.sum_prod_type,FiniteDist.prod_weight]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_irrel,← Finset.sum_mul,first.sum_one,one_mul]
  simp

/-- Translation equivariance proves exact uniformity of the label of a
uniform input, separately from the joint zero-fiber identity. -/
theorem label_uniform_of_translation {V K : Type*} [AddCommGroup V] [AddCommGroup K]
    [Fintype V] [Fintype K]
    (label : V → K) (direction : K →+ V)
    (htranslate : ∀ x k, label (x + direction k) = label x + k) :
    (FiniteDist.uniform V).map label = FiniteDist.uniform K := by
  letI : Nonempty {x : V // label x = 0} :=
    ⟨⟨0 + direction (-label 0), by rw [htranslate]; simp⟩⟩
  have h := congrArg (fun law => law.map (Prod.snd : V × K → K))
    (zeroFiberCoordinates_uniform_joint label direction htranslate)
  simp only [FiniteDist.map_map] at h
  change ((FiniteDist.uniform {x : V // label x = 0}).prod
    (FiniteDist.uniform K)).map Prod.snd = (FiniteDist.uniform V).map label at h
  exact h.symm.trans (zeroFiber_prod_map_snd _ _)

end InfoLossLAR.WorstCase

end P2MDyadicModule8

/- Helper module Solutions.AdvantageBridgeLARToUZF. -/
section P2MDyadicModule9

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

namespace InfoLossLAR.WorstCase

open AFT Matrix QAlgorithms.Complexity

open scoped BigOperators Classical

theorem larRankOnePreprocess_real {F K : Type*} [CommRing F] {d N : ℕ}
    (secret auxiliary : Fin N → F) (direction : K → (Fin d → F))
    (matrix : Matrix (Fin d) (Fin N) F) (error : Fin d → F) (mark : K) :
    larRankOnePreprocess auxiliary direction matrix (matrix.mulVec secret+error) mark =
      (rankOneMatrix secret auxiliary matrix (error+direction mark),mark) := by
  unfold larRankOnePreprocess rankOneMatrix
  rw [add_assoc]

/-- This actual source sampler obeys the proved zero-fiber/label decomposition. -/
theorem larUniformZeroLaw_joint {V K : Type*} [Fintype V] [AddCommGroup V]
    [Fintype K] [AddCommGroup K] (label : V → K) (hzero : label 0=0)
    (direction : K →+ V) (htranslate : ∀ input mark,label (input+direction mark)=label input+mark) :
    ((larUniformZeroLaw label hzero).prod (FiniteDist.uniform K)).map
      (fun pair => (pair.1+direction pair.2,pair.2)) =
      (FiniteDist.uniform V).map (fun input => (input,label input)) := by
  letI : Nonempty {x : V // label x=0} := ⟨⟨0,hzero⟩⟩
  have h := zeroFiberCoordinates_uniform_joint label direction htranslate
  have hi : @Subtype.fintype V (fun x => label x=0)
      (fun x => Classical.propDecidable (label x=0)) inferInstance =
      Subtype.fintype (fun x : V => label x=0) := Subsingleton.elim _ _
  rw [hi] at h
  let source := FiniteDist.uniform {x : V // label x=0}
  let marks := FiniteDist.uniform K
  have hm := FiniteDist.prod_map_functions source marks
    (Subtype.val : {x : V // label x=0} → V) (id : K → K)
  have hid : marks.map id=marks := FiniteDist.uniform_map_equiv (Equiv.refl K)
  rw [hid] at hm
  change ((source.map Subtype.val).prod marks).map (fun pair => (pair.1+direction pair.2,pair.2)) = _
  rw [←hm,FiniteDist.map_map]
  exact h

private theorem lar_map_prod_mix {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (first : FiniteDist A) (second : FiniteDist B) (decode : A × B → C) :
    (first.prod second).map decode = second.mix (fun b => first.map (fun a => decode (a,b))) := by
  ext output
  simp only [FiniteDist.map_weight,FiniteDist.mix_weight,FiniteDist.prod_weight,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : decode (a,b)=output <;> simp [h,mul_comm]

private theorem lar_uniform_prod {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    (FiniteDist.uniform A).prod (FiniteDist.uniform B) = FiniteDist.uniform (A × B) := by
  ext pair
  simp only [FiniteDist.prod_weight,FiniteDist.uniform_weight,Fintype.card_prod,Nat.cast_mul,_root_.mul_inv_rev]
  ring

private theorem lar_prod_map_snd {A B : Type*} [Fintype A] [Fintype B]
    (first : FiniteDist A) (second : FiniteDist B) : (first.prod second).map Prod.snd=second := by
  ext output
  simp only [FiniteDist.map_weight,FiniteDist.prod_weight,Fintype.sum_prod_type]
  simp_rw [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [←Finset.sum_mul,first.sum_one,one_mul]

/-- The actual zero-fiber input sampling reduces to a uniform input with its
correct label, without conditioning on the fixed secret or auxiliary vector. -/
theorem larRankOneRealBlock_zero_disintegration {F K : Type*} [Field F] [Fintype F]
    [Fintype K] [AddCommGroup K] {d N : ℕ}
    (label : (Fin d → F) → K) (hzero : label 0=0) (direction : K →+ (Fin d → F))
    (htranslate : ∀ input mark,label (input+direction mark)=label input+mark)
    (secret auxiliary : Fin N → F) :
    larRankOneRealBlock (larUniformZeroLaw label hzero) direction secret auxiliary =
      (FiniteDist.uniform (Fin d → F)).mix fun input =>
        (FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).map fun matrix =>
          (rankOneMatrix secret auxiliary matrix input,label input) := by
  let kernel := fun pair : (Fin d → F) × K =>
    (FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).map fun matrix =>
      (rankOneMatrix secret auxiliary matrix pair.1,pair.2)
  have hm := FiniteDist.mix_map
    ((larUniformZeroLaw label hzero).prod (FiniteDist.uniform K))
    (fun pair => (pair.1+direction pair.2,pair.2)) kernel
  calc
    _ = (((larUniformZeroLaw label hzero).prod (FiniteDist.uniform K)).map
        (fun pair => (pair.1+direction pair.2,pair.2))).mix kernel := by
      simpa only [larRankOneRealBlock,larRankOnePreprocess_real,kernel] using hm.symm
    _ = ((FiniteDist.uniform (Fin d → F)).map (fun input => (input,label input))).mix kernel := by
      rw [larUniformZeroLaw_joint label hzero direction htranslate]
    _ = _ := FiniteDist.mix_map _ _ _

/-- On alignment, the entire matrix/label block has the genuine real LAR law. -/
theorem larRankOneRealBlock_aligned {F K : Type*} [Field F] [Fintype F]
    [Fintype K] [AddCommGroup K] {d N : ℕ}
    (label : (Fin d → F) → K) (hzero : label 0=0) (direction : K →+ (Fin d → F))
    (htranslate : ∀ input mark,label (input+direction mark)=label input+mark)
    (secret auxiliary : Fin N → F) (halign : auxiliary ⬝ᵥ secret=1) :
    larRankOneRealBlock (larUniformZeroLaw label hzero) direction secret auxiliary =
      (FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).map
        (fun matrix => (matrix,label (matrix.mulVec secret))) := by
  rw [larRankOneRealBlock_zero_disintegration label hzero direction htranslate]
  have hm := lar_map_prod_mix
    (FiniteDist.uniform (Matrix (Fin d) (Fin N) F)) (FiniteDist.uniform (Fin d → F))
    (fun pair => (rankOneMatrix secret auxiliary pair.1 pair.2,label pair.2))
  rw [←hm,lar_uniform_prod]
  exact rankOneMatrix_aligned_joint secret auxiliary halign label

/-- Off alignment, the entire public matrix is uniform independently of the
uniform label, even though the transformed input depends on the shared secret. -/
theorem larRankOneRealBlock_unaligned {F K : Type*} [Field F] [Fintype F]
    [Fintype K] [AddCommGroup K] {d N : ℕ}
    (label : (Fin d → F) → K) (hzero : label 0=0) (direction : K →+ (Fin d → F))
    (htranslate : ∀ input mark,label (input+direction mark)=label input+mark)
    (secret auxiliary : Fin N → F) (hmiss : auxiliary ⬝ᵥ secret≠1) :
    larRankOneRealBlock (larUniformZeroLaw label hzero) direction secret auxiliary =
      (FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).prod (FiniteDist.uniform K) := by
  rw [larRankOneRealBlock_zero_disintegration label hzero direction htranslate,
    rankOneMatrix_unaligned_joint secret auxiliary hmiss,
    label_uniform_of_translation label direction htranslate]

/-- Ideal LWE responses give the exact ideal LAR block for every auxiliary
vector, with no alignment condition and no hidden source assumption. -/
theorem larRankOneIdealBlock_eq {F K : Type*} [Field F] [Fintype F]
    [Fintype K] [Nonempty K] {d N : ℕ}
    (direction : K → (Fin d → F)) (auxiliary : Fin N → F) :
    larRankOneIdealBlock direction auxiliary =
      (FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).prod (FiniteDist.uniform K) := by
  have hmiss : auxiliary ⬝ᵥ (0 : Fin N → F) ≠ 1 := by simp
  have h := FiniteDist.random_equiv_independent
    ((FiniteDist.uniform (Fin d → F)).prod (FiniteDist.uniform K))
    (fun pair => rankOneUnalignedEquiv (d := d) (0 : Fin N → F) auxiliary hmiss (pair.1+direction pair.2))
    Prod.snd
  rw [lar_prod_map_snd] at h
  have hpoint (pair : (Fin d → F) × K) (matrix : Matrix (Fin d) (Fin N) F) :
      larRankOnePreprocess auxiliary direction matrix pair.1 pair.2 =
        (rankOneUnalignedEquiv (0 : Fin N → F) auxiliary hmiss (pair.1+direction pair.2) matrix,pair.2) := by
    change larRankOnePreprocess auxiliary direction matrix pair.1 pair.2 =
      (rankOneMatrix (0 : Fin N → F) auxiliary matrix (pair.1+direction pair.2),pair.2)
    simp only [larRankOnePreprocess,rankOneMatrix,Matrix.mulVec_zero,zero_add]
  simpa only [larRankOneIdealBlock,hpoint] using h

private theorem lar_independent_map {Index Input Output : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Input] [Fintype Output]
    (law : Index → FiniteDist Input) (decode : Index → Input → Output) :
    (FiniteDist.independent law).map (fun word index => decode index (word index)) =
      FiniteDist.independent (fun index => (law index).map (decode index)) := by
  ext values
  simp only [FiniteDist.map_weight,FiniteDist.independent]
  have h := Fintype.prod_sum (fun index point =>
    if decode index point=values index then (law index).weight point else 0)
  apply Eq.trans ?_ h.symm
  apply Finset.sum_congr rfl
  intro word _
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]

private theorem lar_independent_prod_expectation {Index First Second : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype First] [Fintype Second]
    (first : Index → FiniteDist First) (second : Index → FiniteDist Second)
    (value : (Index → First × Second) → ℝ) :
    (FiniteDist.independent (fun index => (first index).prod (second index))).expectation value =
      (FiniteDist.independent first).expectation (fun left =>
        (FiniteDist.independent second).expectation (fun right => value (fun index => (left index,right index)))) := by
  unfold FiniteDist.expectation FiniteDist.independent
  rw [←(Equiv.arrowProdEquivProdArrow Index (fun _ => First) (fun _ => Second)).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  simp only [Equiv.arrowProdEquivProdArrow,Equiv.coe_fn_symm_mk,FiniteDist.prod_weight,
    Finset.prod_mul_distrib,mul_assoc]

private theorem lar_uniform_independent {Index State : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype State] [Nonempty State] :
    FiniteDist.independent (fun _ : Index => FiniteDist.uniform State) = FiniteDist.uniform (Index → State) := by
  ext word
  simp only [FiniteDist.independent,FiniteDist.uniform_weight,Finset.prod_const,
    Finset.card_univ,Fintype.card_fun,Nat.cast_pow,inv_pow]

private theorem lar_uniform_expectation {A : Type*} [Fintype A] [Nonempty A] (test : A → ℝ) :
    (FiniteDist.uniform A).expectation test = avg test := by
  simp only [FiniteDist.expectation,FiniteDist.uniform_weight,avg,←Finset.mul_sum]
  ring

/-- A complete independently sampled ideal matrix/label table is the literal platform experiment. -/
theorem lar_ideal_table_expectation (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [NeZero q] :
    (FiniteDist.independent (fun _ : Fin t =>
      (FiniteDist.uniform (Matrix (Fin d) (Fin N) (ZMod q))).prod
        (FiniteDist.uniform (Fin ℓ → ZMod q)))).expectation
      (fun table => acceptProb D (encInput lam pp (encTable table))) =
      prIdealLAR D lam pp q N d ℓ t := by
  rw [lar_independent_prod_expectation]
  simp only [lar_uniform_independent,lar_uniform_expectation,prIdealLAR]

/-- All real-LAR labels share the fixed secret while their matrices remain independent. -/
theorem lar_real_table_expectation (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) (secret : Fin N → ZMod q) :
    (FiniteDist.independent (fun _ : Fin t =>
      (FiniteDist.uniform (Matrix (Fin d) (Fin N) (ZMod q))).map
        (fun matrix => (matrix,label (matrix.mulVec secret))))).expectation
      (fun table => acceptProb D (encInput lam pp (encTable table))) =
      larSecretAcceptance D lam pp q N d ℓ t label secret := by
  rw [←lar_independent_map,FiniteDist.expectation_map,lar_uniform_independent]
  simp only [lar_uniform_expectation,larSecretAcceptance,Function.comp_def]

/-- The exact whole-table Game 3 to Game 2 comparison, with the same secret
and auxiliary vector fixed for every independently drawn block. -/
theorem larRankOneRealTable_acceptance (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) (hzero : label 0=0)
    (direction : (Fin ℓ → ZMod q) →+ (Fin d → ZMod q))
    (htranslate : ∀ input mark,label (input+direction mark)=label input+mark)
    (secret auxiliary : Fin N → ZMod q) :
    (FiniteDist.independent (fun _ : Fin t =>
      larRankOneRealBlock (larUniformZeroLaw label hzero) direction secret auxiliary)).expectation
      (fun table => acceptProb D (encInput lam pp (encTable table))) =
      if auxiliary ⬝ᵥ secret=1 then larSecretAcceptance D lam pp q N d ℓ t label secret
      else prIdealLAR D lam pp q N d ℓ t := by
  by_cases h : auxiliary ⬝ᵥ secret=1
  · simp only [if_pos h,larRankOneRealBlock_aligned label hzero direction htranslate secret auxiliary h]
    exact lar_real_table_expectation D lam pp q N d ℓ t label secret
  · simp only [if_neg h,larRankOneRealBlock_unaligned label hzero direction htranslate secret auxiliary h]
    exact lar_ideal_table_expectation D lam pp q N d ℓ t

/-- The exact whole-table Game 4 to ideal comparison for each fixed shared auxiliary vector. -/
theorem larRankOneIdealTable_acceptance (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q)) (auxiliary : Fin N → ZMod q) :
    (FiniteDist.independent (fun _ : Fin t => larRankOneIdealBlock direction auxiliary)).expectation
      (fun table => acceptProb D (encInput lam pp (encTable table))) =
        prIdealLAR D lam pp q N d ℓ t := by
  simp only [larRankOneIdealBlock_eq]
  exact lar_ideal_table_expectation D lam pp q N d ℓ t

/-- Game 3 equals Game 2 as a genuine full encoded-table acceptance experiment. -/
theorem prRankOneRealLAR_zero_eq (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) (hzero : label 0=0)
    (direction : (Fin ℓ → ZMod q) →+ (Fin d → ZMod q))
    (htranslate : ∀ input mark,label (input+direction mark)=label input+mark) :
    prRankOneRealLAR D lam pp q N d ℓ t (larUniformZeroLaw label hzero) direction =
      prAlignmentLAR D lam pp q N d ℓ t label := by
  unfold prRankOneRealLAR prAlignmentLAR
  apply congrArg avg
  funext secret
  apply congrArg avg
  funext auxiliary
  rw [larRankOneRealTable_acceptance D lam pp q N d ℓ t label hzero direction htranslate]
  by_cases h : auxiliary ⬝ᵥ secret=1
  · simp only [if_pos h]
    rfl
  · simp only [if_neg h]
    rfl

/-- Game 4 is exactly ideal LAR, without any source approximation loss. -/
theorem prRankOneIdealLAR_eq (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q)) :
    prRankOneIdealLAR D lam pp q N d ℓ t direction = prIdealLAR D lam pp q N d ℓ t := by
  unfold prRankOneIdealLAR
  simp only [larRankOneIdealTable_acceptance]
  have hc : (Fintype.card (Fin N → ZMod q) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [avg,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hc

/-- The explicit uniform-zero-subtype sampler has exactly the platform point masses. -/
theorem larUniformZeroLaw_weight (q d ℓ : ℕ) [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) (hzero : label 0=0)
    (input : Fin d → ZMod q) :
    (larUniformZeroLaw label hzero).weight input = unifZeroFiber label input := by
  letI : Nonempty {x : Fin d → ZMod q // label x=0} := ⟨⟨0,hzero⟩⟩
  have hi : @Subtype.fintype (Fin d → ZMod q) (fun x => label x=0)
      (fun x => Classical.propDecidable (label x=0)) inferInstance =
      Subtype.fintype (fun x : Fin d → ZMod q => label x=0) := Subsingleton.elim _ _
  unfold larUniformZeroLaw unifZeroFiber
  rw [hi]
  exact Integration.uniform_subtype_weight (fun x : Fin d → ZMod q => label x=0) input

private theorem lar_real_block_as_map {F K : Type*} [Field F] [Fintype F]
    [Fintype K] [Nonempty K] {d N : ℕ} (source : FiniteDist (Fin d → F))
    (direction : K → (Fin d → F)) (secret auxiliary : Fin N → F) :
    larRankOneRealBlock source direction secret auxiliary =
      ((FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).prod (source.prod (FiniteDist.uniform K))).map
        (fun draw => larRankOnePreprocess auxiliary direction draw.1
          (draw.1.mulVec secret+draw.2.1) draw.2.2) := by
  unfold larRankOneRealBlock
  exact (lar_map_prod_mix (FiniteDist.uniform (Matrix (Fin d) (Fin N) F))
    (source.prod (FiniteDist.uniform K))
    (fun draw => larRankOnePreprocess auxiliary direction draw.1 (draw.1.mulVec secret+draw.2.1) draw.2.2)).symm

private theorem lar_ideal_block_as_map {F K : Type*} [Field F] [Fintype F]
    [Fintype K] [Nonempty K] {d N : ℕ}
    (direction : K → (Fin d → F)) (auxiliary : Fin N → F) :
    larRankOneIdealBlock direction auxiliary =
      ((FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).prod
        ((FiniteDist.uniform (Fin d → F)).prod (FiniteDist.uniform K))).map
        (fun draw => larRankOnePreprocess auxiliary direction draw.1 draw.2.1 draw.2.2) := by
  unfold larRankOneIdealBlock
  exact (lar_map_prod_mix (FiniteDist.uniform (Matrix (Fin d) (Fin N) F))
    ((FiniteDist.uniform (Fin d → F)).prod (FiniteDist.uniform K))
    (fun draw => larRankOnePreprocess auxiliary direction draw.1 draw.2.1 draw.2.2)).symm

/-- The real block-law experiment expands to the literal weighted LWE table
with fresh uniform reduction labels and the observed responses `A*s+error`. -/
theorem prRankOneRealLAR_unroll (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (source : FiniteDist (Fin d → ZMod q))
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q)) :
    prRankOneRealLAR D lam pp q N d ℓ t source direction =
      avg (fun secret : Fin N → ZMod q => avg (fun auxiliary : Fin N → ZMod q =>
        avg (fun matrices : Fin t → Matrix (Fin d) (Fin N) (ZMod q) =>
          ∑ errors : Fin t → Fin d → ZMod q, (∏ index,source.weight (errors index))*
            avg (fun marks : Fin t → Fin ℓ → ZMod q =>
              acceptProb D (encInput lam pp (encTable (fun index =>
                larRankOnePreprocess auxiliary direction (matrices index)
                  ((matrices index).mulVec secret+errors index) (marks index)))))))) := by
  unfold prRankOneRealLAR
  apply congrArg avg
  funext secret
  apply congrArg avg
  funext auxiliary
  simp_rw [lar_real_block_as_map]
  rw [←lar_independent_map,FiniteDist.expectation_map,lar_independent_prod_expectation,
    lar_uniform_independent,lar_uniform_expectation]
  apply congrArg avg
  funext matrices
  rw [lar_independent_prod_expectation,lar_uniform_independent]
  simp only [Function.comp_def]
  simp_rw [lar_uniform_expectation]
  rfl

/-- The ideal block-law experiment expands to the actual independently
uniform public matrices, LWE responses, and reduction labels. -/
theorem prRankOneIdealLAR_unroll (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q)) :
    prRankOneIdealLAR D lam pp q N d ℓ t direction =
      avg (fun auxiliary : Fin N → ZMod q =>
        avg (fun matrices : Fin t → Matrix (Fin d) (Fin N) (ZMod q) =>
          avg (fun responses : Fin t → Fin d → ZMod q =>
            avg (fun marks : Fin t → Fin ℓ → ZMod q =>
              acceptProb D (encInput lam pp (encTable (fun index =>
                larRankOnePreprocess auxiliary direction (matrices index) (responses index) (marks index)))))))) := by
  unfold prRankOneIdealLAR
  apply congrArg avg
  funext auxiliary
  simp_rw [lar_ideal_block_as_map]
  rw [←lar_independent_map,FiniteDist.expectation_map,lar_independent_prod_expectation,
    lar_uniform_independent,lar_uniform_expectation]
  apply congrArg avg
  funext matrices
  rw [lar_independent_prod_expectation]
  simp only [lar_uniform_independent,lar_uniform_expectation,Function.comp_def]

end InfoLossLAR.WorstCase

end P2MDyadicModule9

/- Helper module Solutions.AdvantageBridgeBoundedUniform. -/
section P2MDyadicModule10

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

namespace InfoLossLAR.WorstCase

open AFT

open scoped BigOperators Classical

/-- Its semantic bijection is proved from the same explicit quotient/remainder algorithm. -/
theorem boundedBaseQDecode_eq (q coordinates : ℕ) (hq : 0<q) (ticket : Fin (q^coordinates)) :
    boundedBaseQDecode q coordinates hq ticket=finFunctionFinEquiv.symm ticket := by
  funext index
  apply Fin.ext
  rfl

theorem boundedFieldDecode_eq (q coordinates : ℕ) [NeZero q] (ticket : Fin (q^coordinates)) :
    boundedFieldDecode q coordinates ticket=boundedFieldEquiv q coordinates ticket := by
  unfold boundedFieldDecode
  rw [boundedBaseQDecode_eq]
  rfl

theorem boundedSplit_eq (F : Type*) (N samples labels : ℕ) (word : Fin (N+samples*labels) → F) :
    boundedSplit F N samples labels word=boundedSplitEquiv F N samples labels word := rfl

end InfoLossLAR.WorstCase

end P2MDyadicModule10

/- Helper module Solutions.AdvantageBridgeBoundedRankOne. -/
section P2MDyadicModule11

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

namespace InfoLossLAR.WorstCase

open AFT Matrix QAlgorithms.Complexity

open scoped BigOperators Classical

private theorem br_uniform_expectation {A : Type*} [Fintype A] [Nonempty A] (test : A → ℝ) :
    (FiniteDist.uniform A).expectation test=avg test := by
  simp only [FiniteDist.expectation,FiniteDist.uniform_weight,avg,←Finset.mul_sum]
  ring

private theorem br_expectation_avg {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (law : FiniteDist A) (test : A → B → ℝ) :
    law.expectation (fun a => avg (test a))=avg (fun b => law.expectation (fun a => test a b)) := by
  simp_rw [←br_uniform_expectation (A := B)]
  exact FiniteDist.expectation_comm law (FiniteDist.uniform B) test

private theorem br_real_expectation (q N d t : ℕ) [NeZero q]
    (source : FiniteDist (Fin d → ZMod q)) (secret : Fin N → ZMod q)
    (test : (Fin t → Matrix (Fin d) (Fin N) (ZMod q) × (Fin d → ZMod q)) → ℝ) :
    (larObservedRealTableLaw q N d t source secret).expectation test =
      avg (fun matrices : Fin t → Matrix (Fin d) (Fin N) (ZMod q) =>
        ∑ errors : Fin t → Fin d → ZMod q,(∏ index,source.weight (errors index))*
          test (fun index => (matrices index,(matrices index).mulVec secret+errors index))) := by
  rw [larObservedRealTableLaw,FiniteDist.expectation_map,FiniteDist.expectation_prod,
    br_uniform_expectation]
  rfl

private theorem br_ideal_expectation (q N d t : ℕ) [NeZero q]
    (test : (Fin t → Matrix (Fin d) (Fin N) (ZMod q) × (Fin d → ZMod q)) → ℝ) :
    (larObservedIdealTableLaw q N d t).expectation test =
      avg (fun matrices : Fin t → Matrix (Fin d) (Fin N) (ZMod q) =>
        avg (fun responses : Fin t → Fin d → ZMod q =>
          test (fun index => (matrices index,responses index)))) := by
  rw [larObservedIdealTableLaw,FiniteDist.expectation_map,FiniteDist.expectation_prod]
  simp only [br_uniform_expectation,Function.comp_def]

/-- The true observed real-table law, followed by independent exact coins,
is precisely the previously proved rank-one real experiment. -/
theorem larObservedRealTableLaw_rankOne (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (source : FiniteDist (Fin d → ZMod q))
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q)) :
    avg (fun secret : Fin N → ZMod q =>
      (larObservedRealTableLaw q N d t source secret).expectation (fun input =>
        avg (fun auxiliary : Fin N → ZMod q =>
          avg (fun marks : Fin t → Fin ℓ → ZMod q =>
            acceptProb D (rankOneEncodedQuery lam pp q N d ℓ t direction (auxiliary,marks) input))))) =
    prRankOneRealLAR D lam pp q N d ℓ t source direction := by
  rw [prRankOneRealLAR_unroll]
  apply congrArg avg
  funext secret
  rw [br_expectation_avg]
  simp_rw [br_real_expectation]
  rfl

/-- The corresponding actual ideal-table experiment is the rank-one ideal game. -/
theorem larObservedIdealTableLaw_rankOne (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q)) :
    (larObservedIdealTableLaw q N d t).expectation (fun input =>
      avg (fun auxiliary : Fin N → ZMod q =>
        avg (fun marks : Fin t → Fin ℓ → ZMod q =>
          acceptProb D (rankOneEncodedQuery lam pp q N d ℓ t direction (auxiliary,marks) input)))) =
    prRankOneIdealLAR D lam pp q N d ℓ t direction := by
  rw [prRankOneIdealLAR_unroll]
  rw [br_expectation_avg]
  simp_rw [br_ideal_expectation]
  rfl

end InfoLossLAR.WorstCase

end P2MDyadicModule11

/- Helper module Integration9_9.TM2PlatformSerialization. -/
section P2MDyadicModule12

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.TM2PlatformSerialization

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open QAlgorithms.Complexity

open Polynomial

/-- A concrete Boolean-list program is a platform string-time certificate. -/
theorem polyTime_of_poly {f : Str → Str} (h : Poly f) : PolyTimeComputable f := by
  let P := (BooleanLists.packProgram.comp h.program).comp BooleanLists.unpackProgram
  exact ⟨(P.congr f (fun _ => rfl)).stock⟩

theorem readUnary_rest_length (xs : Str) : (readUnary xs).2.length ≤ xs.length := by
  simp only [readUnary, List.length_drop]
  omega

@[fun_prop] theorem lengthToken_poly {α : Type} [Coding α] [Inhabited α] :
    Poly (lengthToken : List α → Str) := by
  unfold lengthToken
  fun_prop

@[fun_prop] theorem serializeWords_poly : Poly serializeWords := by
  unfold serializeWords
  have hf : Poly (List.flatten : List Str → Str) := ⟨PolyProgram.listFlatten encodeBool false⟩
  exact Poly.comp Poly.list_append (Poly.pair lengthToken_poly hf)

section RepeatedParser

variable {α : Type} [Coding α] [Inhabited α]

variable (read : Str → Str × α)

lemma readList_rest_length (hr : Poly read)
    (hrest : ∀ xs, (read xs).1.length ≤ xs.length) (xs : Str) :
    (readList read xs).1.length ≤ xs.length := by
  exact (parser_fold_bounds read hr hrest (unarySlots xs) (readUnary xs).2 []).1.trans
    (readUnary_rest_length xs)

end RepeatedParser

end Integration9_9.TM2PlatformSerialization

end P2MDyadicModule12

/- Helper module Solutions.AdvantageBridgeCoinMachine. -/
section P2MDyadicModule13

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.LARCoinMachine

open InfoLossLAR.WorstCase QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open LARPlatformEncoding Polynomial

open scoped BigOperators

private theorem powerFold_value (slots : List Unit) (base value : ℕ) :
    slots.foldl powerStep (base,value)=(base,value*base^slots.length) := by
  induction slots generalizing value with
  | nil => simp
  | cons slot slots ih =>
    simp only [List.foldl_cons,powerStep,ih,List.length_cons,pow_succ]
    congr 1
    ring

theorem powerWithSlots_eq (base : ℕ) (slots : List Unit) : powerWithSlots (base,slots)=base^slots.length := by
  simp only [powerWithSlots,powerFold_value,one_mul]

/-- The machine's dynamic output is exactly the required little-endian base-q digits. -/
theorem decodeBaseQ_eq (base count ticket : ℕ) (slots : List Unit) (hslots : slots.length=count) :
    decodeBaseQ (base,(slots,ticket))=List.ofFn (fun index : Fin count => ticket/base^index.val%base) := by
  apply List.ext_getElem
  · simp only [decodeBaseQ,List.length_map,List.length_range,List.length_ofFn,hslots]
  · intro index hleft hright
    have hi : index<count := by simpa only [List.length_ofFn] using hright
    simp only [decodeBaseQ,List.getElem_map,List.getElem_range,powerWithSlots_eq,List.length_take,
      hslots,Nat.min_eq_left hi.le,List.getElem_ofFn]

private theorem word_value_ofFn (count : ℕ) (tape : Fin count → Bool) :
    Word.value (List.ofFn tape)=∑ index,(tape index).toNat*2^index.val := by
  induction count with
  | zero => simp
  | succ count ih =>
    simp only [List.ofFn_succ,Word.value_cons,Fin.sum_univ_succ,Fin.val_zero,pow_zero,
      mul_one,Fin.val_succ]
    rw [ih]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    rw [pow_succ]
    ring

/-- The actual binary-value machine reads precisely the fair-bit ticket
used by the proved rejection-sampling law. -/
theorem bitValue_boundedBoolTicket (count : ℕ) (tape : Fin count → Bool) :
    bitValue (List.ofFn tape)=(boundedBoolTicket count tape).val := by
  rw [bitValue_eq_word,word_value_ofFn]
  change (∑ index,(tape index).toNat*2^index.val)=
    ∑ index,((finTwoEquiv.symm (tape index)).val)*2^index.val
  apply Finset.sum_congr rfl
  intro index _
  cases tape index <;> rfl

/-- Every field coordinate is produced by the same explicit quotient/remainder
machine, with its actual canonical representative. -/
theorem boundedFieldDecode_val (q count : ℕ) [NeZero q] (ticket : Fin (q^count)) (index : Fin count) :
    (boundedFieldDecode q count ticket index).val=ticket.val/q^index.val%q := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => rfl

end Integration9_9.LARCoinMachine

end P2MDyadicModule13

/- Helper module Integration9_9.FairBitPadding. -/
section P2MDyadicModule14

set_option autoImplicit false

namespace Integration9_9.FairBitPadding

open InfoLossLAR.WorstCase

/-- Relabeling a finite uniform source by a bijection preserves every average. -/
theorem avg_equiv {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : avg (fun a => f (e a)) = avg f := by
  unfold avg
  rw [e.sum_comp, Fintype.card_congr e]

/-- Unused independent randomness has no effect on a finite average. -/
theorem avg_fst {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α → ℝ) : avg (fun p : α × β => f p.1) = avg f := by
  have hα : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [avg, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul, ← Finset.mul_sum]
  field_simp

/-- Padding a fair-bit tape by a fixed number of unused bits preserves its law. -/
theorem avg_prefix_add (n extra : ℕ) (f : (Fin n → Bool) → ℝ) :
    avg (fun tape : Fin (n+extra) → Bool => f (fun i => tape (Fin.castAdd extra i))) = avg f := by
  calc
    _ = avg (fun tape => (fun p : (Fin n → Bool) × (Fin extra → Bool) => f p.1)
          (splitEquiv n extra tape)) := rfl
    _ = avg (fun p : (Fin n → Bool) × (Fin extra → Bool) => f p.1) :=
      avg_equiv (splitEquiv n extra) (fun p => f p.1)
    _ = avg f := avg_fst f

/-- Any upper bound on the required random tape can be used as an exact tape length. -/
theorem avg_prefix {n m : ℕ} (h : n ≤ m) (f : (Fin n → Bool) → ℝ) :
    avg (fun tape : Fin m → Bool => f (fun i => tape (Fin.castLE h i))) = avg f := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa only [Fin.castLE, Fin.castAdd] using avg_prefix_add n extra f

end Integration9_9.FairBitPadding

end P2MDyadicModule14

/- Helper module Solutions.AdvantageBridgeCoinLayout. -/
section P2MDyadicModule15

set_option autoImplicit false

set_option maxHeartbeats 300000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase QAlgorithms.Complexity Function Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime LARPlatformEncoding LARRankOneMachine TM2PlatformSerialization

/-- The genuine coin-first input length is strictly increasing, even when
some coefficients of the fixed polynomial coin budget vanish. -/
theorem coinTotalLength_strictMono (budget : Polynomial ℕ) :
    StrictMono (fun n => budget.eval n+n) := by
  intro a b hab
  have hm := polynomial_eval_mono budget hab.le
  change budget.eval a+a<budget.eval b+b
  omega

theorem coinBaseLength_eq (budget : Polynomial ℕ) (coins input : Str)
    (hc : coins.length=budget.eval input.length) :
    coinBaseLength budget (coins++input)=input.length := by
  let candidates := (List.range ((coins++input).length+1)).filter
    (fun index => decide (budget.eval index+index=(coins++input).length))
  have hn : input.length∈candidates := by
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_range.mpr
      simp only [List.length_append,hc]
      omega
    · simp only [List.length_append,hc,decide_true]
  have hall : ∀ index∈candidates,index=input.length := by
    intro index hi
    have he := (List.mem_filter.mp hi).2
    have heq : budget.eval index+index=budget.eval input.length+input.length := by
      simpa only [decide_eq_true_eq,List.length_append,hc] using he
    exact (coinTotalLength_strictMono budget).injective heq
  cases h : candidates with
  | nil => simp [h] at hn
  | cons first rest =>
    have hf : first=input.length := hall first (by simp [h])
    change (candidates.head?).getD 0=input.length
    simp [h,hf]

theorem coinFirstPair_eq (budget : Polynomial ℕ) (coins input : Str)
    (hc : coins.length=budget.eval input.length) :
    coinFirstPair budget (coins++input)=encPair coins input := by
  unfold coinFirstPair
  rw [coinBaseLength_eq budget coins input hc,←hc]
  dsimp only
  rw [List.take_left,List.drop_left]

end Integration9_9.LARCoinLayout

end P2MDyadicModule15

/- Helper module Solutions.AdvantageBridgeQueryOutput. -/
section P2MDyadicModule16

set_option autoImplicit false

set_option maxHeartbeats 500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime LARRankOneMachine TM2PlatformSerialization

theorem encodeQueryOutput_flag (slots : List Unit) (query : Str) (index : ℕ) (hi : index ≤ slots.length) :
    (encodeQueryOutput slots query)[index]?=some (decide (query.length=index)) := by
  unfold encodeQueryOutput
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_map,List.getElem?_range (show index<slots.length+1 by omega)]
  rfl

theorem encodeQueryOutput_bit (slots : List Unit) (query : Str) (index : ℕ) (hi : index<slots.length) :
    (encodeQueryOutput slots query)[slots.length+1+index]?=some ((query[index]?).getD false) := by
  unfold encodeQueryOutput
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_map,List.length_range,Nat.add_sub_cancel_left]
  rw [List.getElem?_take_of_lt hi]
  by_cases hq : index<query.length
  · rw [List.getElem?_append_left hq,List.getElem?_eq_getElem hq]
    rfl
  · have hnone : query[index]?=none := List.getElem?_eq_none (by omega)
    rw [List.getElem?_append_right (by omega),hnone]
    simp only [Option.getD_none]
    rw [List.getElem?_map,List.getElem?_eq_getElem (show index-query.length<slots.length by omega)]
    rfl

end Integration9_9.LARCoinLayout

end P2MDyadicModule16

/- Helper module Solutions.RegevBridgeToffoli. -/
section P2MDyadicModule17

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

private theorem phase_composition {N : ℕ} (f g : QState N → QState N)
    (a b : Bits N → ℂ)
    (hf : ∀ φ x, f φ x = a x * φ x) (hg : ∀ φ x, g φ x = b x * φ x)
    (φ : QState N) (x : Bits N) : g (f φ) x = b x * a x * φ x := by
  rw [hg, hf, mul_assoc]

private theorem cnot_conj_phase_map {N : ℕ} (i j : Fin N) (hij : i ≠ j) (ψ : QState N)
    (F : QState N → QState N) (a : Bits N → ℂ)
    (hF : ∀ φ x, F φ x = a x * φ x) :
    cnotState i j hij (F (cnotState i j hij ψ)) =
      fun x => a (Function.update x j (xor (x j) (x i))) * ψ x := by
  funext x
  simp only [cnotState, hF, Function.update_self, Function.update_of_ne hij, Bool.xor_assoc,
    Bool.xor_self, Bool.xor_false, Function.update_idem, Function.update_eq_self]

private theorem apply1_tMat_eq_phase {N : ℕ} (i : Fin N) (ψ : QState N) :
    apply1 tMat i ψ = fun x => (if x i then Complex.exp (Complex.I * Real.pi / 4) else 1) * ψ x := by
  funext x
  simp [apply1, tMat]

private theorem inv_sqrt_two_mul_self :
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `shiTof_Ph F a`: `F` acts as multiplication by the diagonal phase `a`. -/
private abbrev shiTof_Ph {N : ℕ} (F : QState N → QState N) (a : Bits N → ℂ) : Prop :=
  ∀ (φ : QState N) (x : Bits N), F φ x = a x * φ x

private lemma shiTof_Ph_comp {N : ℕ} {f g : QState N → QState N} {a b : Bits N → ℂ}
    (hf : shiTof_Ph f a) (hg : shiTof_Ph g b) :
    shiTof_Ph (fun ψ => g (f ψ)) (fun x => b x * a x) := by
  intro ψ x
  exact phase_composition f g a b hf hg ψ x

private lemma shiTof_Ph_conj {N : ℕ} {F : QState N → QState N} {a : Bits N → ℂ}
    (i j : Fin N) (hij : i ≠ j) (hF : shiTof_Ph F a) :
    shiTof_Ph (fun ψ => cnotState i j hij (F (cnotState i j hij ψ)))
      (fun x => a (Function.update x j (xor (x j) (x i)))) := by
  intro ψ x
  exact congrFun (cnot_conj_phase_map i j hij ψ F a hF) x

private lemma shiTof_Ph_t {N : ℕ} (i : Fin N) :
    shiTof_Ph (apply1 tMat i)
      (fun x => if x i then Complex.exp (Complex.I * Real.pi / 4) else 1) := by
  intro φ x
  simp only [apply1_tMat_eq_phase]

/-- `T ^ 7` on one wire, as seven `T` gates. -/
private noncomputable def shiTof_T7 {N : ℕ} (i : Fin N) (ψ : QState N) : QState N :=
  apply1 tMat i (apply1 tMat i (apply1 tMat i (apply1 tMat i
    (apply1 tMat i (apply1 tMat i (apply1 tMat i ψ))))))

private lemma shiTof_Ph_T7 {N : ℕ} (i : Fin N) :
    shiTof_Ph (shiTof_T7 i)
      (fun x => if x i then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) := by
  intro φ x
  simp only [shiTof_T7, apply1_tMat_eq_phase]
  cases hx : x i with
  | false => simp [hx]
  | true =>
      simp only [hx, if_true]
      ring

/-- A `T^7` block conjugated by a CNOT: control `i`, target `j`. -/
private noncomputable def shiTof_cB {N : ℕ} (i j : Fin N) (hij : i ≠ j) (ψ : QState N) :
    QState N :=
  cnotState i j hij (shiTof_T7 j (cnotState i j hij ψ))

private lemma shiTof_Ph_cB {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    shiTof_Ph (shiTof_cB i j hij)
      (fun x => if xor (x j) (x i) then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) := by
  intro φ x
  have h := shiTof_Ph_conj i j hij (shiTof_Ph_T7 j) φ x
  simp only [Function.update_self] at h
  exact h

/-- The three-parity `T` block: `CNOT(p,r) CNOT(q,r) T_r CNOT(q,r) CNOT(p,r)`. -/
private noncomputable def shiTof_cB7 {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r)
    (ψ : QState N) : QState N :=
  cnotState p r hpr (cnotState q r hqr (apply1 tMat r
    (cnotState q r hqr (cnotState p r hpr ψ))))

private lemma shiTof_Ph_cB7 {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r) :
    shiTof_Ph (shiTof_cB7 p q r hpr hqr)
      (fun x => if xor (xor (x r) (x p)) (x q) then
        Complex.exp (Complex.I * Real.pi / 4) else 1) := by
  intro φ x
  have h := shiTof_Ph_conj p r hpr (shiTof_Ph_conj q r hqr (shiTof_Ph_t r)) φ x
  simp only [Function.update_self, Function.update_of_ne hqr] at h
  exact h

/-- The seven block phases multiply to the CCZ sign. -/
private lemma shiTof_phase_prod (a b c : Bool) :
    (if xor (xor c a) b then Complex.exp (Complex.I * Real.pi / 4) else 1) *
      ((if xor c a then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
        ((if xor c b then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
          ((if xor b a then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
            ((if c then Complex.exp (Complex.I * Real.pi / 4) else 1) *
              ((if b then Complex.exp (Complex.I * Real.pi / 4) else 1) *
                (if a then Complex.exp (Complex.I * Real.pi / 4) else 1))))))
      = if a && b && c then (-1 : ℂ) else 1 := by
  let w : ℂ := Complex.exp (Complex.I * Real.pi / 4)
  have h4 : w ^ 4 = -1 := by
    rw [show w ^ 4 = Complex.exp (4 * (Complex.I * Real.pi / 4)) from
      (Complex.exp_nat_mul _ 4).symm]
    convert Complex.exp_pi_mul_I using 1 <;> congr 1 <;> ring
  have h16 : w ^ 16 = 1 := by
    rw [show 16 = 4 * 4 from rfl, pow_mul, h4]
    norm_num
  change (if xor (xor c a) b then w else 1) *
      ((if xor c a then w ^ 7 else 1) *
        ((if xor c b then w ^ 7 else 1) *
          ((if xor b a then w ^ 7 else 1) *
            ((if c then w else 1) * ((if b then w else 1) * (if a then w else 1)))))) = _
  cases a <;> cases b <;> cases c <;> norm_num <;> ring_nf <;> first | exact h16 | exact h4

/-- The CCZ part of the circuit, as a composition of the seven diagonal blocks. -/
private noncomputable def shiTof_cczOp {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (ψ : QState N) : QState N :=
  shiTof_cB7 p q r hpr hqr (shiTof_cB p r hpr (shiTof_cB q r hqr (shiTof_cB p q hpq
    (apply1 tMat r (apply1 tMat q (apply1 tMat p ψ))))))

private lemma shiTof_Ph_ccz {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    shiTof_Ph (shiTof_cczOp p q r hpq hpr hqr)
      (fun x => if x p && x q && x r then (-1 : ℂ) else 1) := by
  have c7 := shiTof_Ph_comp (shiTof_Ph_comp (shiTof_Ph_comp (shiTof_Ph_comp
      (shiTof_Ph_comp (shiTof_Ph_comp (shiTof_Ph_t p) (shiTof_Ph_t q)) (shiTof_Ph_t r))
      (shiTof_Ph_cB p q hpq)) (shiTof_Ph_cB q r hqr)) (shiTof_Ph_cB p r hpr))
      (shiTof_Ph_cB7 p q r hpr hqr)
  intro φ x
  first
    | exact (c7 φ x).trans
        (congrArg (fun z : ℂ => z * φ x) (shiTof_phase_prod (x p) (x q) (x r)))
    | (refine (c7 φ x).trans ?_
       rw [← shiTof_phase_prod (x p) (x q) (x r)])
    | (refine (c7 φ x).trans ?_
       beta_reduce
       rw [shiTof_phase_prod (x p) (x q) (x r)])

private lemma shiTof_hconj {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r)
    (F : QState N → QState N)
    (hF : ∀ (φ : QState N) (y : Bits N),
      F φ y = (if y p && y q && y r then (-1 : ℂ) else 1) * φ y)
    (ψ : QState N) :
    apply1 hMat r (F (apply1 hMat r ψ))
      = fun x => ψ (Function.update x r (xor (x r) (x p && x q))) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 :=
    inv_sqrt_two_mul_self
  funext x
  have hup : ∀ b : Bool, F (apply1 hMat r ψ) (Function.update x r b)
      = (if x p && x q && b then (-1 : ℂ) else 1)
        * ∑ c : Bool, hMat b c * ψ (Function.update x r c) := by
    intro b
    have e1 : Function.update x r b p = x p := Function.update_of_ne hpr b x
    have e2 : Function.update x r b q = x q := Function.update_of_ne hqr b x
    have e3 : Function.update x r b r = b := Function.update_self r b x
    have e4 : apply1 hMat r ψ (Function.update x r b)
        = ∑ c : Bool, hMat b c * ψ (Function.update x r c) := by
      simp only [apply1, Function.update_self, Function.update_idem]
    simp only [hF, e1, e2, e3, e4]
  have main : apply1 hMat r (F (apply1 hMat r ψ)) x
      = ∑ b : Bool, hMat (x r) b * F (apply1 hMat r ψ) (Function.update x r b) := rfl
  rw [main]
  -- PHASE 1: split the outer Bool sum, `hMat` still FOLDED.
  simp only [Fintype.sum_bool]
  -- PHASE 2: expand `F` while `hMat` is still folded, so `hup`'s LHS still matches.
  -- Listing `hup` and `hMat` in one `simp only` unfolded `hMat` inside `F (apply1 hMat r ψ)`
  -- first, `hup` then matched nothing and was silently dropped ("unused simp argument"),
  -- leaving `ring` with two opaque `F …` atoms.
  first
    | rw [hup true, hup false]
    | simp only [hup]
  -- PHASE 3: only now unfold the matrix and split the two inner Bool sums.
  simp only [hMat, Matrix.of_apply, Fintype.sum_bool, Complex.ofReal_inv]
  -- PHASE 4: abstract the irrational AFTER all unfolding, so no `(↑√2)⁻¹` survives
  -- alongside `s` and `hs` applies to every quadratic term.
  set s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ with hsdef
  -- `cases h : e` already substitutes the value, so `simp only [hr, hm]` has nothing to do,
  -- and a no-progress `simp only` is an ERROR in Lean 4 (it killed all four branches).
  cases hr : x r <;> cases hm : (x p && x q) <;> (try simp only [hr, hm]) <;> norm_num <;>
    first
      | linear_combination (2 * ψ (Function.update x r false)) * hs
      | linear_combination (2 * ψ (Function.update x r true)) * hs
      | linear_combination (-2 * ψ (Function.update x r false)) * hs
      | linear_combination (-2 * ψ (Function.update x r true)) * hs

private lemma shiTof_layerOk_map {N : ℕ} (gs : List (Instr N)) :
    ∀ l ∈ gs.map (fun g => [g]), LayerOk l := by
  intro l hl
  simp only [List.mem_map] at hl
  obtain ⟨g, _, hg⟩ := hl
  subst hg
  exact List.pairwise_singleton _ g

private lemma shiTof_run_map {N : ℕ} (gs : List (Instr N)) (ψ : QState N) :
    runLayered (gs.map (fun g => [g])) ψ = gs.foldl (fun st g => Instr.apply g st) ψ := by
  induction gs generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
      have hstep : runLayered ((g :: gs).map (fun z => [z])) ψ
          = runLayered (gs.map (fun z => [z])) (Instr.apply g ψ) := rfl
      rw [hstep, ih, List.foldl_cons]

private lemma shiTof_fold_eq {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (ψ : QState N) :
    (toffoliGates p q r hpq hpr hqr).foldl (fun st g => Instr.apply g st) ψ
      = apply1 hMat r (shiTof_cczOp p q r hpq hpr hqr (apply1 hMat r ψ)) := by
  first
    | rfl
    | simp only [toffoliGates, shiTof_cczOp, shiTof_cB, shiTof_cB7, shiTof_T7,
        List.foldl_cons, List.foldl_nil, Instr.apply]

theorem toffoliCircuit_apply {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (ψ : QState N) :
    runLayered (toffoliCircuit p q r hpq hpr hqr) ψ =
      fun x => ψ (Function.update x r (xor (x r) (x p && x q))) := by
  rw [toffoliCircuit, shiTof_run_map, shiTof_fold_eq]
  exact shiTof_hconj p q r hpr hqr _ (fun φ y => shiTof_Ph_ccz p q r hpq hpr hqr φ y) ψ

theorem toffoliCircuit_wellFormed {N : ℕ} (p q r : Fin N)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∀ layer ∈ toffoliCircuit p q r hpq hpr hqr, LayerOk layer := shiTof_layerOk_map _

end InfoLossLAR.WorstCase

end P2MDyadicModule17

/- Helper module Solutions.RegevBridgeInverseUniform. -/
section P2MDyadicModule18

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem readCircuitInstruction_poly : Poly readCircuitInstruction := by
  unfold readCircuitInstruction
  fun_prop

theorem readCircuitInstruction_rest_length (xs : Str) :
    (readCircuitInstruction xs).1.length ≤ xs.length := by
  unfold readCircuitInstruction
  split_ifs
  · exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans (readUnary_rest_length _))
  · exact (readUnary_rest_length _).trans (readUnary_rest_length _)

@[fun_prop] theorem readCircuitLayer_poly : Poly readCircuitLayer :=
  readList_poly readCircuitInstruction readCircuitInstruction_poly readCircuitInstruction_rest_length

theorem readCircuitLayer_rest_length (xs : Str) :
    (readCircuitLayer xs).1.length ≤ xs.length :=
  readList_rest_length readCircuitInstruction readCircuitInstruction_poly readCircuitInstruction_rest_length xs

@[fun_prop] theorem readCircuitLayers_poly : Poly readCircuitLayers :=
  readList_poly readCircuitLayer readCircuitLayer_poly readCircuitLayer_rest_length

end InfoLossLAR.WorstCase

end P2MDyadicModule18

/- Helper module Solutions.RegevBridgeReversibleCircuit. -/
section P2MDyadicModule19

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

namespace ReversibleGate

theorem compile_apply {n : ℕ} (g : ReversibleGate n) (ψ : QState n) :
    runLayered g.compile ψ = fun x => ψ (g.act x) := by
  cases g with
  | flip i =>
    funext x
    simp only [compile, runLayered, runLayer, List.foldl_cons, List.foldl_nil, Instr.apply, apply1]
    cases hx : x i <;> simp [xMat, act, hx]
  | controlled i j hij => rfl
  | toffoli i j k hij hik hjk => exact toffoliCircuit_apply i j k hij hik hjk ψ

theorem compile_wellFormed {n : ℕ} (g : ReversibleGate n) :
    ∀ layer ∈ g.compile, LayerOk layer := by
  cases g with
  | flip i => simp [compile, LayerOk]
  | controlled i j hij => simp [compile, LayerOk]
  | toffoli i j k hij hik hjk => exact toffoliCircuit_wellFormed i j k hij hik hjk

theorem compile_depth {n : ℕ} (g : ReversibleGate n) : depth g.compile ≤ 37 := by
  cases g <;> simp [compile, depth, toffoliCircuit, toffoliGates]

end ReversibleGate

private theorem runLayered_append {n : ℕ} (c d : Layered n) (ψ : QState n) :
    runLayered (c ++ d) ψ = runLayered d (runLayered c ψ) := List.foldl_append

/-- Amplitude semantics for every input state, including superpositions and garbage. -/
theorem compileReversible_apply {n : ℕ} (gates : List (ReversibleGate n)) (ψ : QState n) :
    runLayered (compileReversible gates) ψ = fun x => ψ ((reversibleAction gates).symm x) := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
    change runLayered (g.compile ++ compileReversible gs) ψ = _
    rw [runLayered_append, ih, g.compile_apply]
    rfl

theorem compileReversible_wellFormed {n : ℕ} (gates : List (ReversibleGate n)) :
    ∀ layer ∈ compileReversible gates, LayerOk layer := by
  intro layer hl
  obtain ⟨g, _, hgl⟩ := List.mem_flatMap.1 hl
  exact g.compile_wellFormed layer hgl

theorem compileReversible_depth {n : ℕ} (gates : List (ReversibleGate n)) :
    depth (compileReversible gates) ≤ 37 * gates.length := by
  induction gates with
  | nil => simp [compileReversible, depth]
  | cons g gs ih =>
    have hg := g.compile_depth
    change (g.compile ++ compileReversible gs).length ≤ _
    simp only [List.length_append, List.length_cons]
    change g.compile.length ≤ 37 at hg
    change (compileReversible gs).length ≤ _ at ih
    omega

/-- A computational basis input is sent to the exact classical output. -/
theorem compileReversible_basis {n : ℕ} (gates : List (ReversibleGate n)) (x : Bits n) :
    runLayered (compileReversible gates) (fun y => if y = x then (1 : ℂ) else 0) =
      fun y => if y = reversibleAction gates x then 1 else 0 := by
  rw [compileReversible_apply]
  funext y
  congr 1
  exact propext (Equiv.symm_apply_eq _)

end InfoLossLAR.WorstCase

end P2MDyadicModule19

/- Helper module Solutions.RegevBridgeReversibleUniform. -/
section P2MDyadicModule20

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem toffoliInstructionWords_poly :
    Poly (fun x : Str × Str × Str => toffoliInstructionWords x.1 x.2.1 x.2.2) := by
  unfold toffoliInstructionWords
  fun_prop

@[fun_prop] theorem readReversibleInstruction_poly : Poly readReversibleInstruction := by
  unfold readReversibleInstruction
  fun_prop

theorem readReversibleInstruction_rest_length (xs : Str) :
    (readReversibleInstruction xs).1.length ≤ xs.length := by
  unfold readReversibleInstruction
  split_ifs
  · exact (readUnary_rest_length _).trans (readUnary_rest_length _)
  · exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans (readUnary_rest_length _))
  · exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans
      ((readUnary_rest_length _).trans (readUnary_rest_length _)))

private theorem reversibleUniformUnaryWidth (n : ℕ) (xs : Str) : inputWidth (encNat n ++ xs) = n := by
  simpa only [encNat, List.append_assoc, List.singleton_append] using inputWidth_prefix n xs

theorem readReversibleInstruction_append {n : ℕ} (g : ReversibleGate n) (xs : Str) :
    readReversibleInstruction (g.code ++ xs) = (xs, g.compile.flatten.map encInstr) := by
  cases g <;> simp only [ReversibleGate.code, List.append_assoc, readReversibleInstruction,
    reversibleUniformUnaryWidth, readUnary_append] <;> norm_num <;> rfl

@[fun_prop] theorem readReversibleProgram_poly : Poly readReversibleProgram :=
  readList_poly readReversibleInstruction readReversibleInstruction_poly readReversibleInstruction_rest_length

theorem readReversibleProgram_append {n : ℕ} (gates : List (ReversibleGate n)) (xs : Str) :
    readReversibleProgram (encStr (gates.map ReversibleGate.code) ++ xs) =
      (xs, gates.map (fun g => g.compile.flatten.map encInstr)) :=
  readList_append_mapped readReversibleInstruction ReversibleGate.code
    (fun g => g.compile.flatten.map encInstr) readReversibleInstruction_append gates xs

private theorem compiledWords {n : ℕ} (gates : List (ReversibleGate n)) :
    ((gates.map (fun g => g.compile.flatten.map encInstr)).flatten).map (fun word => [word]) =
      (compileReversible gates).map (List.map encInstr) := by
  induction gates with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.flatten_cons, List.map_append, compileReversible,
      List.flatMap_cons] at ih ⊢
    rw [ih]
    congr 1
    cases g <;> rfl

@[fun_prop] theorem compileReversibleDescription_poly : Poly compileReversibleDescription := by
  unfold compileReversibleDescription
  have hf : Poly (List.flatten : List (List Str) → List Str) :=
    ⟨PolyProgram.listFlatten (encodeList encodeBool) []⟩
  fun_prop

theorem compileReversibleDescription_code (F : ReversibleFamily) (n : ℕ) :
    compileReversibleDescription (F.code n) = encFamilyAt F.compile n := by
  unfold ReversibleFamily.code compileReversibleDescription
  simp only [List.append_assoc, readUnary_append]
  have h := readReversibleProgram_append (F.gates n) []
  simp only [List.append_nil] at h
  rw [h]
  have hh := congrArg (fun xs : List (List Str) => serializeWords (xs.map serializeWords))
    (compiledWords (F.gates n))
  simp only [List.map_map, Function.comp_def] at hh
  rw [hh]
  simp only [serializeWords_eq, encFamilyAt, ReversibleFamily.compile, encCirc, List.append_assoc]
  rfl

end InfoLossLAR.WorstCase

end P2MDyadicModule20

/- Helper module Solutions.RegevBridgeBooleanCircuit. -/
section P2MDyadicModule21

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

namespace BooleanGate

theorem assign_other {n : ℕ} (g : BooleanGate n) (x : Bits n) (i : Fin n)
    (hi : i ≠ g.target) : g.assign x i = x i := Function.update_of_ne hi _ _

theorem compile_length {n : ℕ} (g : BooleanGate n) : g.compile.length ≤ 2 := by
  cases g <;> simp only [compile] <;> (try split_ifs) <;> simp

theorem compile_action {n : ℕ} (g : BooleanGate n) (x : Bits n)
    (hz : x g.target = false) : reversibleAction g.compile x = g.assign x := by
  cases g with
  | constant t b =>
    cases b <;> simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value]
  | copy s t h =>
    simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value]
  | negate s t h =>
    funext i
    by_cases hi : i = t
    · subst i
      cases hv : x s <;>
        simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value,
          Function.update_of_ne h]
    · simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value,
        Function.update_of_ne hi]
  | xor a b t ha hb =>
    simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value,
      Function.update_of_ne hb]
  | and a b t ha hb =>
    by_cases hab : a = b
    · subst b
      simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value]
    · simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value]

end BooleanGate

theorem reversibleAction_append {n : ℕ} (a b : List (ReversibleGate n)) :
    reversibleAction (a ++ b) = (reversibleAction a).trans (reversibleAction b) := by
  induction a with
  | nil => rfl
  | cons g a ih =>
    simp only [List.cons_append, reversibleAction, ih]
    rfl

/-- Complete Boolean-program semantics, with all intermediate values retained. -/
theorem booleanToReversible_action {n : ℕ} (gates : List (BooleanGate n))
    (hf : BooleanFresh gates) (x : Bits n)
    (hz : ∀ g ∈ gates, x g.target = false) :
    reversibleAction (booleanToReversible gates) x = booleanRun gates x := by
  induction gates generalizing x with
  | nil => rfl
  | cons g gates ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.1 hf
    have hzero : ∀ h ∈ gates, g.assign x h.target = false := by
      intro h hh
      rw [g.assign_other x h.target (Ne.symm (hhead h hh))]
      exact hz h (by simp [hh])
    change reversibleAction (g.compile ++ booleanToReversible gates) x = _
    rw [reversibleAction_append]
    change reversibleAction (booleanToReversible gates) (reversibleAction g.compile x) = _
    rw [g.compile_action x (hz g (by simp)), ih htail _ hzero]
    rfl

theorem booleanToReversible_length {n : ℕ} (gates : List (BooleanGate n)) :
    (booleanToReversible gates).length ≤ 2 * gates.length := by
  induction gates with
  | nil => simp [booleanToReversible]
  | cons g gates ih =>
    have hg := g.compile_length
    change (g.compile ++ booleanToReversible gates).length ≤ _
    simp only [List.length_append, List.length_cons]
    omega

theorem booleanCircuit_depth {n : ℕ} (gates : List (BooleanGate n)) :
    depth (compileReversible (booleanToReversible gates)) ≤ 74 * gates.length := by
  have h := (compileReversible_depth (booleanToReversible gates)).trans
    (Nat.mul_le_mul_left 37 (booleanToReversible_length gates))
  omega

end InfoLossLAR.WorstCase

end P2MDyadicModule21

/- Helper module Solutions.RegevBridgeBooleanUniform. -/
section P2MDyadicModule22

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem readBooleanInstruction_poly : Poly readBooleanInstruction := by
  unfold readBooleanInstruction
  fun_prop

theorem readBooleanInstruction_rest_length (xs : Str) :
    (readBooleanInstruction xs).1.length ≤ xs.length := by
  unfold readBooleanInstruction
  dsimp only
  split_ifs <;>
    first
      | exact (readUnary_rest_length _).trans (readUnary_rest_length _)
      | exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans (readUnary_rest_length _))
      | exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans
          ((readUnary_rest_length _).trans (readUnary_rest_length _)))

private theorem unaryWidth_append (n : ℕ) (xs : Str) : inputWidth (encNat n ++ xs) = n := by
  simpa only [encNat, List.append_assoc, List.singleton_append] using inputWidth_prefix n xs

private theorem unaryWidth (n : ℕ) : inputWidth (encNat n) = n := by
  simpa using unaryWidth_append n []

theorem readBooleanInstruction_append {n : ℕ} (g : BooleanGate n) (xs : Str) :
    readBooleanInstruction (g.code ++ xs) = (xs, g.compile.map ReversibleGate.code) := by
  cases g with
  | constant t b =>
    cases b <;> simp only [BooleanGate.code, Bool.false_eq_true, ite_false, ite_true,
      readBooleanInstruction, List.append_assoc, readUnary_append, unaryWidth_append] <;> norm_num <;> rfl
  | copy s t h =>
    simp only [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
      unaryWidth_append] <;> norm_num <;> rfl
  | negate s t h =>
    simp only [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
      unaryWidth_append] <;> norm_num <;> rfl
  | xor a b t ha hb =>
    simp only [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
      unaryWidth_append] <;> norm_num <;> rfl
  | and a b t ha hb =>
    by_cases hab : a = b
    · subst b
      simp [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
        unaryWidth_append, unaryWidth, BooleanGate.compile, ReversibleGate.code]
    · have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
      simp [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
        unaryWidth_append, unaryWidth, BooleanGate.compile, ReversibleGate.code, hab, habv]

@[fun_prop] theorem readBooleanProgram_poly : Poly readBooleanProgram :=
  readList_poly readBooleanInstruction readBooleanInstruction_poly readBooleanInstruction_rest_length

theorem readBooleanProgram_append {n : ℕ} (gates : List (BooleanGate n)) (xs : Str) :
    readBooleanProgram (encStr (gates.map BooleanGate.code) ++ xs) =
      (xs, gates.map (fun g => g.compile.map ReversibleGate.code)) :=
  readList_append_mapped readBooleanInstruction BooleanGate.code
    (fun g => g.compile.map ReversibleGate.code) readBooleanInstruction_append gates xs

@[fun_prop] theorem compileBooleanDescription_poly : Poly compileBooleanDescription := by
  unfold compileBooleanDescription
  have hf : Poly (List.flatten : List (List Str) → List Str) :=
    ⟨PolyProgram.listFlatten (encodeList encodeBool) []⟩
  fun_prop

theorem compileBooleanDescription_code (F : BooleanFamily) (n : ℕ) :
    compileBooleanDescription (F.code n) = F.reversible.code n := by
  unfold BooleanFamily.code compileBooleanDescription
  simp only [List.append_assoc, readUnary_append]
  have h := readBooleanProgram_append (F.gates n) []
  simp only [List.append_nil] at h
  rw [h, serializeWords_eq]
  have hh : (List.map (fun g => List.map ReversibleGate.code g.compile) (F.gates n)).flatten =
      (booleanToReversible (F.gates n)).map ReversibleGate.code := by
    simp only [booleanToReversible, List.flatMap_def, List.map_flatten, List.map_map, Function.comp_def]
  rw [hh]
  simp only [ReversibleFamily.code, BooleanFamily.reversible, List.append_assoc]

end InfoLossLAR.WorstCase

end P2MDyadicModule22

/- Helper module Solutions.RegevBridgeBooleanProgram. -/
section P2MDyadicModule23

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

namespace BooleanOp

theorem toGate_target {total : ℕ} (op : BooleanOp) (target : Fin total) :
    (op.toGate target).target = target := by
  cases op <;> simp only [toGate] <;> (try split_ifs) <;> rfl

theorem toGate_value {total : ℕ} (op : BooleanOp) (target : Fin total)
    (hv : op.Valid target.val) (s : ℕ → Bool) :
    (op.toGate target).value (fun i => s i.val) = op.eval s := by
  cases op <;> simp_all [Valid, sources, toGate, BooleanGate.value, eval]

theorem toGate_assign {total : ℕ} (op : BooleanOp) (target : Fin total)
    (hv : op.Valid target.val) (s : ℕ → Bool) :
    (op.toGate target).assign (fun i => s i.val) = fun i => op.assign target.val s i.val := by
  funext i
  rw [BooleanGate.assign, toGate_target, toGate_value op target hv]
  by_cases hi : i = target
  · subst i; simp [assign]
  · have hval : i.val ≠ target.val := fun h => hi (Fin.ext h)
    simp [assign, Function.update_of_ne hi, Function.update_of_ne hval]

end BooleanOp

namespace BooleanProgram

theorem target_range {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) (g : BooleanGate total) (hg : g ∈ gates start ops h) :
    start ≤ g.target.val ∧ g.target.val < start + ops.length := by
  induction ops generalizing start with
  | nil => simp [gates] at hg
  | cons op rest ih =>
    simp only [gates, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp only [BooleanOp.toGate_target, List.length_cons]; omega
    · have hh := ih (start := start + 1) _ hg
      simp only [List.length_cons]; omega

theorem fresh {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) : BooleanFresh (gates start ops h) := by
  induction ops generalizing start with
  | nil => exact List.Pairwise.nil
  | cons op rest ih =>
    apply List.pairwise_cons.2
    constructor
    · intro g hg heq
      have hh := (target_range rest _ g hg).1
      rw [BooleanOp.toGate_target] at heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_mk] at hv
      omega
    · exact ih _

theorem run_below (start : ℕ) (ops : List BooleanOp) (s : ℕ → Bool)
    (i : ℕ) (hi : i < start) : run start ops s i = s i := by
  induction ops generalizing start s with
  | nil => rfl
  | cons op rest ih =>
    rw [run, ih (start + 1) (op.assign start s) (by omega)]
    exact Function.update_of_ne (by omega) _ _

theorem run_append (start : ℕ) (a b : List BooleanOp) (s : ℕ → Bool) :
    run start (a ++ b) s = run (start + a.length) b (run start a s) := by
  induction a generalizing start s with
  | nil => simp [run]
  | cons op a ih =>
    simp only [List.cons_append, run, ih, List.length_cons]
    rw [show start + 1 + a.length = start + (a.length + 1) by omega]

theorem semantics {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) (hv : Valid start ops) (s : ℕ → Bool) :
    booleanRun (gates start ops h) (fun i => s i.val) = fun i => run start ops s i.val := by
  induction ops generalizing start s with
  | nil => rfl
  | cons op rest ih =>
    change booleanRun (gates (start + 1) rest _) ((op.toGate _).assign (fun i => s i.val)) = _
    rw [BooleanOp.toGate_assign op _ hv.1, ih _ hv.2]
    rfl

theorem reversible_semantics {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) (hv : Valid start ops) (s : ℕ → Bool)
    (hz : ∀ i, start ≤ i → i < start + ops.length → s i = false) :
    reversibleAction (booleanToReversible (gates start ops h)) (fun i => s i.val) =
      fun i => run start ops s i.val := by
  rw [booleanToReversible_action _ (fresh ops h)]
  · exact semantics ops h hv s
  · intro g hg
    obtain ⟨hl, hu⟩ := target_range ops h g hg
    exact hz _ hl hu

/-- The literal Clifford+T implementation has exactly the fresh-program basis semantics. -/
theorem circuit_basis {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) (hv : Valid start ops) (s : ℕ → Bool)
    (hz : ∀ i, start ≤ i → i < start + ops.length → s i = false) :
    runLayered (compileReversible (booleanToReversible (gates start ops h)))
      (fun x => if x = (fun i => s i.val) then (1 : ℂ) else 0) =
        fun x => if x = (fun i => run start ops s i.val) then 1 else 0 := by
  rw [compileReversible_basis, reversible_semantics ops h hv s hz]

theorem circuit_depth {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) :
    depth (compileReversible (booleanToReversible (gates start ops h))) ≤ 74 * ops.length := by
  simpa only [gates_length] using booleanCircuit_depth (gates start ops h)

end BooleanProgram

end InfoLossLAR.WorstCase

end P2MDyadicModule23

/- Helper module Solutions.RegevBridgeBooleanExpr. -/
section P2MDyadicModule24

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

namespace BooleanExpr

theorem eval_congr {bound : ℕ} (e : BooleanExpr) (hv : e.Valid bound)
    {s t : ℕ → Bool} (h : ∀ i, i < bound → s i = t i) : e.eval s = e.eval t := by
  induction e with
  | input i => exact h i hv
  | constant b => rfl
  | negate a ih => exact congrArg Bool.not (ih hv)
  | xor a b ia ib => exact congrArg₂ Bool.xor (ia hv.1) (ib hv.2)
  | and a b ia ib => exact congrArg₂ Bool.and (ia hv.1) (ib hv.2)

private theorem singleton_at (start : ℕ) (op : BooleanOp) (s : ℕ → Bool) :
    BooleanProgram.run start [op] s start = op.eval s := by
  simp [BooleanProgram.run, BooleanOp.assign]

private theorem append_singleton_at (start : ℕ) (ops : List BooleanOp) (op : BooleanOp)
    (s : ℕ → Bool) :
    BooleanProgram.run start (ops ++ [op]) s (start + ops.length) =
      op.eval (BooleanProgram.run start ops s) := by
  rw [BooleanProgram.run_append, singleton_at]

theorem compile_eval (e : BooleanExpr) (start : ℕ) (hv : e.Valid start) (s : ℕ → Bool) :
    BooleanProgram.run start (e.compile start).1 s (e.compile start).2 = e.eval s := by
  induction e generalizing start s with
  | input i => rfl
  | constant b => exact singleton_at start (.constant b) s
  | negate a ih =>
    simp only [compile, append_singleton_at, BooleanOp.eval, eval]
    rw [ih start hv]
  | xor a b ia ib | and a b ia ib =>
    have hca := (a.compile_valid start hv.1).2
    have hcb := b.valid_mono hv.2 (Nat.le_add_right start a.size)
    have hb := ib (start + a.size) hcb (BooleanProgram.run start (a.compile start).1 s)
    have heq : b.eval (BooleanProgram.run start (a.compile start).1 s) = b.eval s :=
      b.eval_congr hv.2 (fun i hi => BooleanProgram.run_below _ _ _ i hi)
    rw [heq] at hb
    simp only [compile, compile_length]
    rw [show start + a.size + b.size = start +
      ((a.compile start).1 ++ (b.compile (start + a.size)).1).length by simp; omega,
      append_singleton_at, BooleanProgram.run_append]
    simp only [BooleanOp.eval, compile_length, eval]
    rw [BooleanProgram.run_below _ _ _ _ hca, ia start hv.1, hb]

end BooleanExpr

end InfoLossLAR.WorstCase

end P2MDyadicModule24

/- Helper module Solutions.RegevBridgeBooleanBundle. -/
section P2MDyadicModule25

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

namespace BooleanExpr

theorem lookup_eval {α : Type} [Fintype α] [DecidableEq α]
    (table : α → Bool) (inputs : α → BooleanExpr) (s : ℕ → Bool) (actual : α)
    (h : ∀ a, (inputs a).eval s = decide (a = actual)) :
    (lookup table inputs).eval s = table actual := by
  rw [Bool.eq_iff_iff]
  simp only [lookup, eval_any_true, List.mem_map, List.mem_filter,
    Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, he⟩
    have heq : a = actual := by simpa only [h, decide_eq_true_eq] using he
    simpa only [heq] using ha
  · intro ha
    exact ⟨inputs actual, ⟨actual, ha, rfl⟩, by simp [h]⟩

theorem compileMany_eval (start : ℕ) (es : List BooleanExpr)
    (h : ∀ e ∈ es, e.Valid start) (s : ℕ → Bool) :
    (compileMany start es).2.map (BooleanProgram.run start (compileMany start es).1 s) =
      es.map (fun e => e.eval s) := by
  induction es generalizing start s with
  | nil => rfl
  | cons e es ih =>
    have he := h e (by simp)
    have hout := (e.compile_valid start he).2
    have ht := ih (start + e.size)
      (fun a ha => a.valid_mono (h a (by simp [ha])) (Nat.le_add_right _ _))
      (BooleanProgram.run start (e.compile start).1 s)
    have href : es.map (fun a => a.eval (BooleanProgram.run start (e.compile start).1 s)) =
        es.map (fun a => a.eval s) := by
      apply List.map_congr_left
      intro a ha
      exact a.eval_congr (h a (by simp [ha])) (fun i hi => BooleanProgram.run_below _ _ _ i hi)
    rw [href] at ht
    simp only [compileMany, compile_length, List.map_cons, BooleanProgram.run_append]
    rw [BooleanProgram.run_below _ _ _ _ hout, e.compile_eval start he, ht]

theorem multiplex_eval {α : Type} [Fintype α] [DecidableEq α]
    (control payload : α → BooleanExpr) (s : ℕ → Bool) (actual : α)
    (h : ∀ a, (control a).eval s = decide (a = actual)) :
    (multiplex control payload).eval s = (payload actual).eval s := by
  rw [Bool.eq_iff_iff]
  simp only [multiplex, eval_any_true, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, he⟩
    simp only [eval, Bool.and_eq_true, h, decide_eq_true_eq] at he
    simpa only [he.1] using he.2
  · intro hp
    exact ⟨.and (control actual) (payload actual), ⟨actual, rfl⟩, by simp [eval, h, hp]⟩

end BooleanExpr

end InfoLossLAR.WorstCase

end P2MDyadicModule25

/- Helper module Solutions.RegevBridgeTM2Symbolic. -/
section P2MDyadicModule26

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

variable {K Λ σ : Type} [DecidableEq K] [DecidableEq Λ] [DecidableEq σ] [Fintype σ]

namespace Symbolic

variable {width : ℕ}

theorem load_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (f : σ → σ) :
    Encodes (sym.load f) {cfg with var := f cfg.var} bits := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  exact BooleanExpr.lookup_eval _ _ _ cfg.var h.state

theorem push_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (k : K) (f : σ → Bool) :
    Encodes (sym.push k f) {cfg with stk := Function.update cfg.stk k (f cfg.var :: cfg.stk k)} bits := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  by_cases hj : j = k
  · subst j
    simp only [push, Function.update_self, ↓reduceIte]
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceDIte, List.getElem?_cons_zero]
      exact BooleanExpr.lookup_eval _ _ _ cfg.var h.state
    · simp only [hi, ↓reduceDIte]
      rw [h.stack]
      congr 1
      have he : i.val = (i.val - 1) + 1 := by omega
      conv_rhs => rw [he]
      simp only [List.getElem?_cons_succ]
  · simpa only [push, hj, ↓reduceIte, Function.update_of_ne hj] using h.stack j i b

theorem read_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (hw : 0 < width)
    (k : K) (f : σ → Option Bool → σ) :
    Encodes (sym.read hw k f) {cfg with var := f cfg.var (cfg.stk k).head?} bits := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  apply BooleanExpr.lookup_eval _ _ _ (cfg.var, (cfg.stk k).head?)
  intro a
  simp only [BooleanExpr.eval, h.state, h.stack]
  simp [Prod.ext_iff, List.head?_eq_getElem?]

theorem pop_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (k : K)
    (hsize : (cfg.stk k).length ≤ width) :
    Encodes (sym.pop k) {cfg with stk := Function.update cfg.stk k (cfg.stk k).tail} bits := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  by_cases hj : j = k
  · subst j
    simp only [pop, Function.update_self, ↓reduceIte]
    by_cases hi : i.val + 1 < width
    · simp only [hi, ↓reduceDIte, h.stack]
      congr 1
      simp
    · simp only [hi, ↓reduceDIte, BooleanExpr.eval]
      have he : (cfg.stk k).tail[i.val]? = none :=
        List.getElem?_eq_none (by simp only [List.length_tail]; omega)
      rw [he]
  · simpa only [pop, hj, ↓reduceIte, Function.update_of_ne hj] using h.stack j i b

theorem jump_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (f : σ → Λ) :
    Encodes (sym.jump f) {cfg with l := some (f cfg.var)} bits := by
  refine ⟨?_, h.state, h.stack⟩
  intro l
  exact BooleanExpr.lookup_eval _ _ _ cfg.var h.state

theorem halt_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) :
    Encodes sym.halt {cfg with l := none} bits := ⟨fun _ => rfl, h.state, h.stack⟩

theorem select_encodes (condition : BooleanExpr) (a b : Symbolic K Λ σ width)
    (cfgA cfgB : Configuration K Λ σ) (bits : ℕ → Bool)
    (ha : Encodes a cfgA bits) (hb : Encodes b cfgB bits) :
    Encodes (select condition a b) (if condition.eval bits then cfgA else cfgB) bits := by
  cases hc : condition.eval bits
  · refine ⟨?_, ?_, ?_⟩
    · intro l; simpa only [select, BooleanExpr.eval_select, hc, Bool.false_eq_true, ↓reduceIte] using hb.label l
    · intro v; simpa only [select, BooleanExpr.eval_select, hc, Bool.false_eq_true, ↓reduceIte] using hb.state v
    · intro k i b; simpa only [select, BooleanExpr.eval_select, hc, Bool.false_eq_true, ↓reduceIte] using hb.stack k i b
  · refine ⟨?_, ?_, ?_⟩
    · intro l; simpa only [select, BooleanExpr.eval_select, hc, ↓reduceIte] using ha.label l
    · intro v; simpa only [select, BooleanExpr.eval_select, hc, ↓reduceIte] using ha.state v
    · intro k i b; simpa only [select, BooleanExpr.eval_select, hc, ↓reduceIte] using ha.stack k i b

end Symbolic

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule26

/- Helper module Solutions.RegevBridgeTM2Transition. -/
section P2MDyadicModule27

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

/-- The stack-size premise is precisely the allocated capacity, including all pushes in this step. -/
theorem auxiliary_encodes (hw : 0 < width) (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ) (bits : ℕ → Bool)
    (h : Encodes sym cfg bits) (hsize : stackSize cfg.stk + pushBound q ≤ width) :
    Encodes (auxiliary hw q sym) (TM2.stepAux q cfg.var cfg.stk) bits := by
  induction q generalizing sym cfg with
  | push k f q ih =>
    have hs : stackSize (Function.update cfg.stk k (f cfg.var :: cfg.stk k)) ≤ stackSize cfg.stk + 1 :=
      stackSize_update_le cfg.stk k _ _ (Nat.le_add_right _ _)
        (by simpa only [List.length_cons] using Nat.succ_le_succ (length_le_stackSize cfg.stk k))
    exact ih (sym.push k f) {cfg with stk := Function.update cfg.stk k (f cfg.var :: cfg.stk k)}
      (sym.push_encodes cfg bits h k f) (by simp only [pushBound] at hsize; dsimp only; omega)
  | peek k f q ih =>
    exact ih (sym.read hw k f) {cfg with var := f cfg.var (cfg.stk k).head?}
      (sym.read_encodes cfg bits h hw k f) hsize
  | pop k f q ih =>
    have hs : stackSize (Function.update cfg.stk k (cfg.stk k).tail) ≤ stackSize cfg.stk :=
      stackSize_update_le cfg.stk k _ _ le_rfl
        (by simp only [List.length_tail]; exact (Nat.sub_le _ _).trans (length_le_stackSize cfg.stk k))
    have hr := sym.read_encodes cfg bits h hw k f
    have hp := (sym.read hw k f).pop_encodes {cfg with var := f cfg.var (cfg.stk k).head?}
      bits hr k ((length_le_stackSize cfg.stk k).trans (by simp only [pushBound] at hsize; omega))
    exact ih ((sym.read hw k f).pop k)
      {cfg with var := f cfg.var (cfg.stk k).head?, stk := Function.update cfg.stk k (cfg.stk k).tail}
      hp (by simp only [pushBound] at hsize; dsimp only; omega)
  | load f q ih =>
    exact ih (sym.load f) {cfg with var := f cfg.var} (sym.load_encodes cfg bits h f) hsize
  | branch f q r iq ir =>
    have hq := iq sym cfg h (by simp only [pushBound] at hsize; have := le_max_left (pushBound q) (pushBound r); omega)
    have hr := ir sym cfg h (by simp only [pushBound] at hsize; have := le_max_right (pushBound q) (pushBound r); omega)
    have he := Symbolic.select_encodes (BooleanExpr.lookup f sym.state)
      (auxiliary hw q sym) (auxiliary hw r sym) _ _ bits hq hr
    rw [BooleanExpr.lookup_eval f sym.state bits cfg.var h.state] at he
    cases hf : f cfg.var <;> simpa only [auxiliary, TM2.stepAux, hf, Bool.cond_false,
      Bool.cond_true, Bool.false_eq_true, ↓reduceIte] using he
  | goto f => exact sym.jump_encodes cfg bits h f
  | halt => exact sym.halt_encodes cfg bits h

theorem multiplex_encodes {α : Type} [Fintype α] [DecidableEq α]
    (control : α → BooleanExpr) (choices : α → Symbolic K Λ σ width)
    (bits : ℕ → Bool) (actual : α) (cfg : Configuration K Λ σ)
    (hc : ∀ a, (control a).eval bits = decide (a = actual))
    (h : Encodes (choices actual) cfg bits) : Encodes (multiplex control choices) cfg bits := by
  constructor
  · intro l
    rw [multiplex, BooleanExpr.multiplex_eval control _ bits actual hc]
    exact h.label l
  · intro v
    rw [multiplex, BooleanExpr.multiplex_eval control _ bits actual hc]
    exact h.state v
  · intro k i b
    rw [multiplex, BooleanExpr.multiplex_eval control _ bits actual hc]
    exact h.stack k i b

theorem transition_encodes (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ) (bits : ℕ → Bool)
    (h : Encodes sym cfg bits) (hsize : stackSize cfg.stk + programPushBound program ≤ width) :
    Encodes (transition hw program sym) (stickyStep program cfg) bits := by
  apply multiplex_encodes sym.label _ bits cfg.l _ h.label
  cases hl : cfg.l with
  | none => simpa only [hl, Option.elim_none, stickyStep] using h
  | some l =>
    have hq : pushBound (program l) ≤ programPushBound program :=
      Finset.le_sup (f := fun l => pushBound (program l)) (Finset.mem_univ l)
    simpa only [hl, Option.elim_some, stickyStep] using
      auxiliary_encodes hw (program l) sym cfg bits h (by omega)

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule27

/- Helper module Solutions.RegevBridgeBooleanSize. -/
section P2MDyadicModule28

set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace InfoLossLAR.WorstCase.BooleanExpr

theorem size_any_le (es : List BooleanExpr) (bound : ℕ)
    (h : ∀ e ∈ es, e.size ≤ bound) : (any es).size ≤ (bound + 4) * es.length + 1 := by
  induction es with
  | nil => simp [any, size]
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [any, size_or, List.length_cons]
    nlinarith

theorem size_lookup_le {α : Type} [Fintype α]
    (table : α → Bool) (inputs : α → BooleanExpr) (bound : ℕ)
    (h : ∀ a, (inputs a).size ≤ bound) :
    (lookup table inputs).size ≤ (bound + 4) * Fintype.card α + 1 := by
  have he := size_any_le ((Finset.univ.toList.filter table).map inputs) bound (by
    intro e he
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 he
    exact h a)
  have hl : (Finset.univ.toList.filter table).length ≤ Fintype.card α := by
    simpa only [Finset.length_toList, Finset.card_univ] using
      List.length_filter_le table (Finset.univ.toList : List α)
  simp only [List.length_map] at he
  simpa only [lookup] using he.trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hl) 1)

theorem size_multiplex_le {α : Type} [Fintype α]
    (control payload : α → BooleanExpr) (controlBound payloadBound : ℕ)
    (hc : ∀ a, (control a).size ≤ controlBound)
    (hp : ∀ a, (payload a).size ≤ payloadBound) :
    (multiplex control payload).size ≤
      (controlBound + payloadBound + 5) * Fintype.card α + 1 := by
  have he := size_any_le (Finset.univ.toList.map (fun a => and (control a) (payload a)))
    (controlBound + payloadBound + 1) (by
      intro e he
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 he
      simp only [size]
      have := hc a
      have := hp a
      omega)
  simpa only [multiplex, List.length_map, Finset.length_toList, Finset.card_univ, Nat.add_assoc]
    using he

end InfoLossLAR.WorstCase.BooleanExpr

end P2MDyadicModule28

/- Helper module Solutions.RegevBridgeTM2CompileStep. -/
section P2MDyadicModule29

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

namespace Symbolic

end Symbolic

namespace Symbolic

/-- Each output reference evaluates to the formula it replaces after fresh compilation. -/
theorem output_eval (sym : Symbolic K Λ σ width) (start : ℕ) (h : sym.Valid start)
    (bits : ℕ → Bool) (i : Slot K Λ σ width) :
    BooleanProgram.run start (sym.compiled start).1 bits (sym.output start i) = (sym.get i).eval bits := by
  have he := BooleanExpr.compileMany_eval start sym.formulas (sym.formulas_valid h) bits
  have hi := congrArg (fun xs : List Bool => xs[(slotEquiv K Λ σ width i).val]?) he
  simp only [List.getElem?_map] at hi
  have ho : (sym.compiled start).2[(slotEquiv K Λ σ width i).val]? = some (sym.output start i) :=
    List.getElem?_eq_getElem _
  change (sym.compiled start).2[(slotEquiv K Λ σ width i).val]?.map
    (BooleanProgram.run start (sym.compiled start).1 bits) = _ at hi
  rw [ho] at hi
  simp only [formulas, List.getElem?_ofFn, dif_pos (slotEquiv K Λ σ width i).isLt,
    Fin.eta, Equiv.symm_apply_apply, Option.map_some, Option.some.injEq] at hi
  exact hi

theorem rebound_encodes (sym : Symbolic K Λ σ width) (start : ℕ) (h : sym.Valid start)
    (cfg : Configuration K Λ σ) (bits : ℕ → Bool) (he : Encodes sym cfg bits) :
    Encodes (sym.rebound start) cfg (BooleanProgram.run start (sym.compiled start).1 bits) := by
  constructor
  · intro l
    rw [rebound, ofSlots, BooleanExpr.eval, output_eval sym start h bits (.inl l)]
    exact he.label l
  · intro v
    rw [rebound, ofSlots, BooleanExpr.eval, output_eval sym start h bits (.inr (.inl v))]
    exact he.state v
  · intro k i b
    rw [rebound, ofSlots, BooleanExpr.eval, output_eval sym start h bits (.inr (.inr (k, i, b)))]
    exact he.stack k i b

end Symbolic

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule29

/- Helper module Solutions.RegevBridgeBooleanRPN. -/
section P2MDyadicModule30

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem step_poly : Poly (fun x : State × Token => step x.1 x.2) := by
  unfold step emit
  fun_prop

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule30

/- Helper module Solutions.RegevBridgeBooleanRPNRun. -/
section P2MDyadicModule31

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open Polynomial

theorem Bounded.mono {N M : ℕ} {s : State} (h : Bounded N s) (hm : N ≤ M) :
    Bounded M s := by
  exact ⟨h.slots.trans hm, h.operands.trans hm, h.nodes.trans hm,
    fun x hx => (h.refs x hx).trans hm,
    fun x hx => ⟨(h.code x hx).1.trans hm, (h.code x hx).2.1.trans hm,
      (h.code x hx).2.2.trans hm⟩⟩

theorem getD_bound (xs : List ℕ) (i N : ℕ) (h : ∀ x ∈ xs, x.bits.length ≤ N) :
    ((xs[i]?).getD 0).bits.length ≤ N := by
  by_cases hi : i < xs.length
  · simp only [List.getElem?_eq_getElem hi, Option.getD_some]
    exact h _ (List.getElem_mem hi)
  · rw [List.getElem?_eq_none (show xs.length ≤ i by omega)]
    simp

theorem emit_bounded {N : ℕ} {s : State} (h : Bounded N s) (x : Node)
    (hx : NodeBound (N+1) x) (rest : List ℕ) (hl : rest.length ≤ N)
    (hr : ∀ a ∈ rest, a.bits.length ≤ N+1) : Bounded (N+1) (emit s x rest) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [emit] using Nat.add_le_add_right h.slots 1
  · simpa [emit] using Nat.add_le_add_right hl 1
  · simpa [emit] using Nat.add_le_add_right h.nodes 1
  · intro a ha
    simp only [emit, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact (NatBinary.length_le_height (Nat.lt_two_pow_self.le)).trans (Nat.add_le_add_right h.slots 1)
    · exact hr a ha
  · intro a ha
    simp only [emit, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact (h.mono (Nat.le_succ N)).code a ha
    · exact hx

theorem step_bounded {N : ℕ} {s : State} (h : Bounded N s) (hN : 3 ≤ N)
    (token : Token) (ht : token.2.bits.length ≤ N+1) : Bounded (N+1) (step s token) := by
  have hh := h.mono (Nat.le_succ N)
  have h0 := getD_bound s.2.1 0 (N+1) hh.refs
  have h1 := getD_bound s.2.1 1 (N+1) hh.refs
  have tailLen : s.2.1.tail.length ≤ N := by rw [List.length_tail]; exact (Nat.sub_le _ _).trans h.operands
  have tailTailLen : s.2.1.tail.tail.length ≤ N :=
    by rw [List.length_tail]; omega
  have tailRefs : ∀ a ∈ s.2.1.tail, a.bits.length ≤ N+1 :=
    fun a ha => hh.refs a (List.mem_of_mem_tail ha)
  have tailTailRefs : ∀ a ∈ s.2.1.tail.tail, a.bits.length ≤ N+1 :=
    fun a ha => tailRefs a (List.mem_of_mem_tail ha)
  unfold step
  split
  · refine ⟨hh.slots, ?_, hh.nodes, ?_, hh.code⟩
    · simpa using Nat.add_le_add_right h.operands 1
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ht
      · exact hh.refs x hx
  · split
    · apply emit_bounded h _ _ _ h.operands hh.refs
      norm_num [NodeBound]
    · split
      · apply emit_bounded h _ _ _ h.operands hh.refs
        norm_num [NodeBound]
      · split
        · apply emit_bounded h _ _ _ tailLen tailRefs
          change (3:ℕ).bits.length ≤ N+1 ∧ _ ≤ N+1 ∧ 0 ≤ N+1
          rw [show (3:ℕ).bits.length = 2 by decide]
          exact ⟨by omega, h0, Nat.zero_le _⟩
        · split
          · apply emit_bounded h _ _ _ tailTailLen tailTailRefs
            change (_:ℕ).bits.length ≤ N+1 ∧ _ ≤ N+1 ∧ _ ≤ N+1
            norm_num only [show (4:ℕ).bits.length = 3 by decide, show (5:ℕ).bits.length = 3 by decide]
            exact ⟨by omega, h1, h0⟩
          · apply emit_bounded h _ _ _ tailTailLen tailTailRefs
            change (_:ℕ).bits.length ≤ N+1 ∧ _ ≤ N+1 ∧ _ ≤ N+1
            norm_num only [show (4:ℕ).bits.length = 3 by decide, show (5:ℕ).bits.length = 3 by decide]
            exact ⟨by omega, h1, h0⟩

theorem run_bounded (tokens : List Token) {N : ℕ} {s : State} (h : Bounded N s)
    (hN : 3 ≤ N) (ht : ∀ t ∈ tokens, t.2.bits.length ≤ N) :
    Bounded (N+tokens.length) (run tokens s) := by
  induction tokens generalizing N s with
  | nil => simpa [run] using h
  | cons t ts ih =>
    have hs := step_bounded h hN t ((ht t (by simp)).trans (Nat.le_succ N))
    have hh := ih hs (by omega) (fun u hu => (ht u (by simp [hu])).trans (Nat.le_succ N))
    simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem encodedUnit_length (xs : List Unit) : (enc xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (encodeList (fun _ : Unit => []) (x::xs)).length = _
    rw [EncodedList.cons_length]
    change (encodeList (fun _ : Unit => []) xs).length = xs.length at ih
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.length_cons]
    omega

theorem bounded_of_encoding (s : State) : Bounded (enc s).length s := by
  have hs := encodedUnit_length s.1
  have ho := EncodedList.length_le Nat.bits s.2.1
  have hn := EncodedList.length_le (enc : Node → List Bool) s.2.2
  have he : (enc s).length = 2*(enc s.1).length+1+2*(enc s.2.1).length+1+(enc s.2.2).length := by
    simp only [enc, Coding.encode, encodePair_length]; omega
  change s.2.1.length ≤ (enc s.2.1).length at ho
  change s.2.2.length ≤ (enc s.2.2).length at hn
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · intro x hx
    have hh := EncodedList.member_length Nat.bits s.2.1 x hx
    change x.bits.length ≤ (enc s.2.1).length at hh
    omega
  · intro x hx
    have hh := EncodedList.member_length (enc : Node → List Bool) s.2.2 x hx
    change (enc x).length ≤ (enc s.2.2).length at hh
    have he' : (enc x).length = 2*x.1.bits.length+1+2*x.2.1.bits.length+1+x.2.2.bits.length := by
      simp only [enc, Coding.encode, encodePair_length]; omega
    exact ⟨by omega, by omega, by omega⟩

theorem encoding_bound {N : ℕ} {s : State} (h : Bounded N s) :
    (enc s).length ≤ 20*(N+1)^2 := by
  have hs := encodedUnit_length s.1
  have ho := EncodedList.length_bound Nat.bits s.2.1 N h.refs
  have hn := EncodedList.length_bound (enc : Node → List Bool) s.2.2 (5*N+2) (by
    intro x hx
    have hb := h.code x hx
    rcases hb with ⟨hb1, hb2, hb3⟩
    change (encodePair Nat.bits (encodePair Nat.bits Nat.bits) x).length ≤ _
    simp only [encodePair_length]
    omega)
  have ho' : (enc s.2.1).length ≤ N*(2*N+1) := ho.trans (Nat.mul_le_mul_right _ h.operands)
  have hn' : (enc s.2.2).length ≤ N*(2*(5*N+2)+1) := hn.trans (Nat.mul_le_mul_right _ h.nodes)
  change (encodePair (enc : List Unit → List Bool) (encodePair enc enc) s).length ≤ _
  simp only [encodePair_length]
  nlinarith [h.slots]

theorem run_partial_bound (tokens : List Token) (s : State) (pre suf : List Token)
    (he : tokens = pre ++ suf) :
    (enc (run pre s)).length ≤ 20*(2*(enc (tokens,s)).length+4)^2 := by
  let L := (enc (tokens,s)).length
  have heL : L = 2*(enc tokens).length+1+(enc s).length := encodePair_length _ _ _
  have hpenc : (enc pre).length ≤ (enc tokens).length := by
    change (encodeList enc pre).length ≤ (encodeList enc tokens).length
    rw [he, EncodedList.append, List.length_append]; omega
  have hplen : pre.length ≤ L := by
    have hh := EncodedList.length_le (enc : Token → List Bool) pre
    change pre.length ≤ (enc pre).length at hh
    omega
  have hs := (bounded_of_encoding s).mono (show (enc s).length ≤ L+3 by omega)
  have ht : ∀ t ∈ pre, t.2.bits.length ≤ L+3 := by
    intro t ht
    have hh := EncodedList.member_length (enc : Token → List Bool) pre t ht
    change (enc t).length ≤ (enc pre).length at hh
    have hte : (enc t).length = 2*t.1.bits.length+1+t.2.bits.length := encodePair_length _ _ _
    omega
  have hb := run_bounded pre hs (by omega) ht
  have hb' := hb.mono (show L+3+pre.length ≤ 2*L+3 by omega)
  have hh := encoding_bound hb'
  simpa [L, Nat.add_assoc] using hh

@[fun_prop] theorem run_poly : Poly (fun x : List Token × State => run x.1 x.2) := by
  apply Poly.of_program
  exact step_poly.program.listFold (0,0) (20*(2*X+4)^2) (by
    intro tokens s pre suf he
    simp only [eval_mul, eval_ofNat, eval_pow, eval_add, eval_X]
    change (enc (run pre s)).length ≤ 20*(2*(enc (tokens,s)).length+4)^2
    exact run_partial_bound tokens s pre suf he)

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule31

/- Helper module Solutions.RegevBridgeBooleanCodePoly. -/
section P2MDyadicModule32

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

namespace CodePoly

variable {α β : Type} [Coding α] [Coding β]

theorem comp {f : β → BooleanExpr} {g : α → β} (hf : CodePoly f) (hg : Poly g) :
    CodePoly (fun a => f (g a)) := Automatic.Poly.comp (f := fun b => code (f b)) (g := g) hf hg

theorem input {f : α → ℕ} (hf : Poly f) : CodePoly (fun a => .input (f a)) := by
  unfold CodePoly code
  fun_prop

theorem constant (b : Bool) : CodePoly (fun _ : α => .constant b) := by
  unfold CodePoly
  exact Automatic.Poly.const _

theorem negate {f : α → BooleanExpr} (hf : CodePoly f) : CodePoly (fun a => .negate (f a)) := by
  unfold CodePoly at hf ⊢
  change Poly (fun a => code (f a) ++ [(3,0)])
  fun_prop

theorem and {f g : α → BooleanExpr} (hf : CodePoly f) (hg : CodePoly g) :
    CodePoly (fun a => .and (f a) (g a)) := by
  unfold CodePoly at hf hg ⊢
  change Poly (fun a => code (f a) ++ code (g a) ++ [(5,0)])
  fun_prop

theorem or {f g : α → BooleanExpr} (hf : CodePoly f) (hg : CodePoly g) :
    CodePoly (fun a => BooleanExpr.or (f a) (g a)) := by
  exact (hf.negate.and hg.negate).negate

theorem select {f g h : α → BooleanExpr} (hf : CodePoly f) (hg : CodePoly g) (hh : CodePoly h) :
    CodePoly (fun a => BooleanExpr.select (f a) (g a) (h a)) := by
  exact (hf.and hg).or (hf.negate.and hh)

theorem ite {p : α → Bool} {f g : α → BooleanExpr} (hp : Poly p)
    (hf : CodePoly f) (hg : CodePoly g) :
    CodePoly (fun a => if p a then f a else g a) := by
  change Poly (fun a => code (if p a then f a else g a))
  have he : (fun a => code (if p a then f a else g a)) =
      (fun a => if p a then code (f a) else code (g a)) := by funext a; split <;> rfl
  rw [he]
  exact Poly.ite hp hf hg

theorem any {ι : Type} (indices : List ι) (f : ι → α → BooleanExpr)
    (hf : ∀ i ∈ indices, CodePoly (f i)) :
    CodePoly (fun a => BooleanExpr.any (indices.map (fun i => f i a))) := by
  induction indices with
  | nil => exact constant false
  | cons i is ih =>
    exact (hf i (by simp)).or (ih (fun j hj => hf j (by simp [hj])))

theorem lookup {ι : Type} [Fintype ι] (table : ι → Bool) (f : ι → α → BooleanExpr)
    (hf : ∀ i, CodePoly (f i)) :
    CodePoly (fun a => BooleanExpr.lookup table (fun i => f i a)) :=
  any _ f (fun i _ => hf i)

theorem multiplex {ι : Type} [Fintype ι] (f g : ι → α → BooleanExpr)
    (hf : ∀ i, CodePoly (f i)) (hg : ∀ i, CodePoly (g i)) :
    CodePoly (fun a => BooleanExpr.multiplex (fun i => f i a) (fun i => g i a)) :=
  any _ _ (fun i _ => (hf i).and (hg i))

end CodePoly

@[fun_prop] theorem compileTokens_poly :
    Poly (fun x : List Token × List Unit => compileTokens x.1 x.2) := by
  unfold compileTokens
  fun_prop

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule32

/- Helper module Solutions.RegevBridgeTM2CodeFamily. -/
section P2MDyadicModule33

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ α : Type} [DecidableEq K] [DecidableEq Λ] [DecidableEq σ] [Fintype σ]

namespace CodeFamily

variable [Coding α]

theorem load_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (f : σ → σ) : (sym.load f).IsPoly :=
  ⟨h.label, fun v => CodePoly.lookup _ sym.state h.state, h.stack⟩

theorem push_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (k : K) (f : σ → Bool) :
    (sym.push k f).IsPoly := by
  refine ⟨h.label, h.state, ?_⟩
  intro j b
  by_cases hj : j = k
  · subst j
    simp only [push, ↓reduceIte]
    have hi : Poly (fun x : α × ℕ => decide (x.2 = 0)) := by fun_prop
    have hf := CodePoly.lookup (fun v => decide (b = some (f v)))
      (fun v (x : α × ℕ) => sym.state v x.1) (fun v => (h.state v).comp (by fun_prop))
    have ht := (h.stack k b).comp (show Poly (fun x : α × ℕ => (x.1,x.2-1)) by fun_prop)
    simpa only [decide_eq_true_eq] using CodePoly.ite hi hf ht
  · simpa only [push, hj, ↓reduceIte] using h.stack j b

theorem read_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (k : K) (f : σ → Option Bool → σ) :
    (sym.read k f).IsPoly := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  change CodePoly (fun a => BooleanExpr.lookup (fun u : σ × Option Bool => decide (v = f u.1 u.2)) (fun u => .and (sym.state u.1 a) (sym.stack k u.2 (a,0))))
  apply CodePoly.lookup
  intro u
  exact (h.state u.1).and ((h.stack k u.2).comp (by fun_prop))

theorem pop_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (width : α → ℕ)
    (hw : Poly width) (k : K) : (sym.pop width k).IsPoly := by
  refine ⟨h.label, h.state, ?_⟩
  intro j b
  by_cases hj : j = k
  · subst j
    simp only [pop, ↓reduceIte]
    have hi : Poly (fun x : α × ℕ => decide (x.2+1 < width x.1)) := by fun_prop
    have ht := (h.stack k b).comp (show Poly (fun x : α × ℕ => (x.1,x.2+1)) by fun_prop)
    simpa only [decide_eq_true_eq] using CodePoly.ite hi ht (CodePoly.constant (decide (b=none)))
  · simpa only [pop, hj, ↓reduceIte] using h.stack j b

theorem jump_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (f : σ → Λ) : (sym.jump f).IsPoly :=
  ⟨fun l => CodePoly.lookup _ sym.state h.state, h.state, h.stack⟩

theorem halt_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) : sym.halt.IsPoly :=
  ⟨fun l => CodePoly.constant (decide (l=none)), h.state, h.stack⟩

theorem select_poly (condition : α → BooleanExpr) (a b : CodeFamily K Λ σ α)
    (hc : CodePoly condition) (ha : a.IsPoly) (hb : b.IsPoly) : (select condition a b).IsPoly :=
  ⟨fun l => hc.select (ha.label l) (hb.label l),
    fun v => hc.select (ha.state v) (hb.state v),
    fun k v => (hc.comp (by fun_prop)).select (ha.stack k v) (hb.stack k v)⟩

end CodeFamily

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule33

/- Helper module Solutions.RegevBridgeTM2CodeTransition. -/
section P2MDyadicModule34

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeFamily

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ α : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable [Coding α]

theorem auxiliaryCode_poly (width : α → ℕ) (hw : Poly width)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) :
    (auxiliaryCode width q sym).IsPoly := by
  induction q generalizing sym with
  | push k f q ih => exact ih _ (sym.push_poly h k f)
  | peek k f q ih => exact ih _ (sym.read_poly h k f)
  | pop k f q ih => exact ih _ ((sym.read k f).pop_poly (sym.read_poly h k f) width hw k)
  | load f q ih => exact ih _ (sym.load_poly h f)
  | branch f q r iq ir =>
    exact select_poly _ _ _ (CodePoly.lookup f sym.state h.state) (iq _ h) (ir _ h)
  | goto f => exact sym.jump_poly h f
  | halt => exact sym.halt_poly h

theorem multiplexCode_poly {ι : Type} [Fintype ι]
    (control : ι → α → BooleanExpr) (choices : ι → CodeFamily K Λ σ α)
    (hc : ∀ i, CodePoly (control i)) (hp : ∀ i, (choices i).IsPoly) :
    (multiplexCode control choices).IsPoly :=
  ⟨fun l => CodePoly.multiplex _ _ hc (fun i => (hp i).label l),
    fun v => CodePoly.multiplex _ _ hc (fun i => (hp i).state v),
    fun k b => CodePoly.multiplex _ _ (fun i => (hc i).comp (by fun_prop)) (fun i => (hp i).stack k b)⟩

theorem transitionCode_poly (width : α → ℕ) (hw : Poly width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) :
    (transitionCode width program sym).IsPoly := by
  apply multiplexCode_poly _ _ h.label
  intro l
  cases l with
  | none => exact h
  | some l => exact auxiliaryCode_poly width hw (program l) sym h

end InfoLossLAR.WorstCase.TM2Boolean.CodeFamily

end P2MDyadicModule34

/- Helper module Solutions.RegevBridgeTM2CodeEnumeration. -/
section P2MDyadicModule35

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

theorem fixed_flatMap_poly {α β ι : Type} [Coding α] [Coding β] [Inhabited β]
    (indices : List ι) (f : ι → α → List β) (hf : ∀ i ∈ indices, Poly (f i)) :
    Poly (fun a => indices.flatMap (fun i => f i a)) := by
  induction indices with
  | nil => exact Automatic.Poly.const []
  | cons i is ih =>
    have hi := hf i (by simp)
    have ht := ih (fun j hj => hf j (by simp [hj]))
    change Poly (fun a => f i a ++ is.flatMap (fun j => f j a))
    fun_prop

namespace CodeFamily

variable {K Λ σ α : Type} [Fintype K] [Fintype Λ] [Fintype σ]

theorem codes_poly [Coding α] (sym : CodeFamily K Λ σ α) (h : sym.IsPoly)
    (width : α → List Unit) (hw : Poly width) : Poly (sym.codes width) := by
  have hlabel := fixed_flatMap_poly (enumerate (Fintype.equivFin (Option Λ)))
    (fun l a => code (sym.label l a)) (fun l _ => h.label l)
  have hstate := fixed_flatMap_poly (enumerate (Fintype.equivFin σ))
    (fun v a => code (sym.state v a)) (fun v _ => h.state v)
  have hstack : ∀ k, Poly (fun a : α =>
      (List.range (width a).length).flatMap (fun i =>
        (enumerate (Fintype.equivFin (Option Bool))).flatMap (fun b => code (sym.stack k b (a,i))))) := by
    intro k
    have hcell := fixed_flatMap_poly (enumerate (Fintype.equivFin (Option Bool)))
      (fun b (x : α × ℕ) => code (sym.stack k b x)) (fun b _ => h.stack k b)
    apply Automatic.Poly.list_flatMap hcell
    exact Automatic.Poly.comp (f := fun xs : List Unit => List.range xs.length)
      (g := width) Automatic.Poly.list_indices hw
  have hstackAll := fixed_flatMap_poly (enumerate (Fintype.equivFin K)) _ (fun k _ => hstack k)
  unfold codes
  fun_prop

theorem compile_poly [Coding α] (sym : CodeFamily K Λ σ α) (h : sym.IsPoly)
    (width slots : α → List Unit) (hw : Poly width) (hs : Poly slots) : Poly (sym.compile width slots) := by
  have hc := sym.codes_poly h width hw
  unfold compile
  fun_prop

end CodeFamily

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule35

/- Helper module Solutions.RegevBridgeTM2BoundedRun. -/
section P2MDyadicModule36

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing StateTransition

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

theorem stickyStep_size (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (cfg : Configuration K Λ σ) :
    stackSize (stickyStep program cfg).stk ≤ stackSize cfg.stk + programPushBound program := by
  cases hl : cfg.l with
  | none => simpa only [stickyStep, hl, Option.elim_none] using Nat.le_add_right (stackSize cfg.stk) _
  | some l =>
    have hc := stepAux_stackSize_le (program l) cfg.var cfg.stk
    have hb : pushBound (program l) ≤ programPushBound program :=
      Finset.le_sup (f := fun l => pushBound (program l)) (Finset.mem_univ l)
    simpa only [stickyStep, hl, Option.elim_some] using hc.trans (Nat.add_le_add_left hb _)

/-- Full bounded execution: each step is compiled and its formula outputs are rebound to fresh wires. -/
theorem compileRun_encodes (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ) (bits : ℕ → Bool)
    (hv : sym.Valid start) (he : Encodes sym cfg bits)
    (hsize : stackSize cfg.stk + programPushBound program * ticks ≤ width) :
    Encodes (compileRun hw program ticks start sym).2 ((stickyStep program)^[ticks] cfg)
      (BooleanProgram.run start (compileRun hw program ticks start sym).1 bits) := by
  induction ticks generalizing start sym cfg bits with
  | zero => exact he
  | succ ticks ih =>
    have ht := transition_valid hw program sym hv
    have hcap : stackSize cfg.stk + programPushBound program ≤ width := by nlinarith
    have hs := transition_encodes hw program sym cfg bits he hcap
    have hf := (transition hw program sym).rebound_encodes start ht _ bits hs
    have hv' := (transition hw program sym).rebound_valid start ht
    have hg := stickyStep_size program cfg
    have hremaining : stackSize (stickyStep program cfg).stk + programPushBound program * ticks ≤ width := by
      nlinarith
    have hh := ih _ _ _ _ hv' hf hremaining
    simpa only [compileRun, BooleanProgram.run_append, Function.iterate_succ_apply] using hh

theorem stickyStep_of_step (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (a b : Configuration K Λ σ) (h : TM2.step program a = some b) : stickyStep program a = b := by
  rcases a with ⟨l, v, stackStore⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l => simpa only [TM2.step, Option.some.injEq, stickyStep, Option.elim_some] using h

theorem stickyStep_of_halted (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (a : Configuration K Λ σ) (h : a.l = none) : stickyStep program a = a := by
  simp only [stickyStep, h, Option.elim_none]

private theorem iterate_none {α : Type} (step : α → Option α) (n : ℕ) :
    ((fun c : Option α => c.bind step)^[n]) none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply, Option.bind_none] using ih

theorem sticky_iterate_of_steps (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (steps : ℕ) (a b : Configuration K Λ σ)
    (h : ((fun c : Option (Configuration K Λ σ) => c.bind (TM2.step program))^[steps]) (some a) = some b) :
    (stickyStep program)^[steps] a = b := by
  induction steps generalizing a with
  | zero => simpa using h
  | succ steps ih =>
    rw [Function.iterate_succ_apply] at h
    cases hs : TM2.step program a with
    | none => simp only [Option.bind_some, hs, iterate_none] at h; contradiction
    | some next =>
      simp only [Option.bind_some, hs] at h
      rw [Function.iterate_succ_apply, stickyStep_of_step program a next hs]
      exact ih next h

/-- A successful machine's budget can be padded after halt without changing its output. -/
theorem sticky_iterate_of_outputs (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (a b : Configuration K Λ σ) (ticks : ℕ)
    (h : EvalsToInTime (TM2.step program) a (some b) ticks) (hb : b.l = none) :
    (stickyStep program)^[ticks] a = b := by
  have hs := sticky_iterate_of_steps program h.steps a b h.evals_in_steps
  have he : ticks = (ticks - h.steps) + h.steps := by have := h.steps_le_m; omega
  rw [he, Function.iterate_add_apply, hs]
  exact Function.iterate_fixed (stickyStep_of_halted program b hb) _

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule36

/- Helper module Solutions.RegevBridgeTM2Size. -/
section P2MDyadicModule37

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

namespace Symbolic

theorem Bounded.mono {small big : ℕ} {sym : Symbolic K Λ σ width}
    (h : sym.Bounded small) (hle : small ≤ big) : sym.Bounded big :=
  ⟨fun l => (h.label l).trans hle, fun v => (h.state v).trans hle,
    fun k i b => (h.stack k i b).trans hle⟩

private theorem old_le_operation (bound : ℕ) : bound ≤ operationBound σ bound := by
  unfold operationBound; omega

private theorem lookup_le_operation (bound : ℕ) : lookupBound σ bound ≤ operationBound σ bound := by
  unfold operationBound; omega

private theorem read_le_operation (bound : ℕ) : readBound σ bound ≤ operationBound σ bound := by
  unfold operationBound; omega

theorem load_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) (f : σ → σ) :
    (sym.load f).Bounded (operationBound σ bound) := by
  refine ⟨fun l => (h.label l).trans (old_le_operation bound), ?_,
    fun k i b => (h.stack k i b).trans (old_le_operation bound)⟩
  intro v
  exact (BooleanExpr.size_lookup_le _ _ bound h.state).trans (lookup_le_operation bound)

theorem push_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) (k : K) (f : σ → Bool) :
    (sym.push k f).Bounded (operationBound σ bound) := by
  refine ⟨fun l => (h.label l).trans (old_le_operation bound),
    fun v => (h.state v).trans (old_le_operation bound), ?_⟩
  intro j i b
  dsimp only [push]
  split_ifs
  · exact (BooleanExpr.size_lookup_le _ _ bound h.state).trans (lookup_le_operation bound)
  · exact (h.stack _ _ _).trans (old_le_operation bound)
  · exact (h.stack _ _ _).trans (old_le_operation bound)

theorem read_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound)
    (hw : 0 < width) (k : K) (f : σ → Option Bool → σ) :
    (sym.read hw k f).Bounded (operationBound σ bound) := by
  refine ⟨fun l => (h.label l).trans (old_le_operation bound), ?_,
    fun k i b => (h.stack k i b).trans (old_le_operation bound)⟩
  intro v
  have hi : ∀ a : σ × Option Bool,
      (BooleanExpr.and (sym.state a.1) (sym.stack k ⟨0, hw⟩ a.2)).size ≤ 2 * bound + 1 := by
    intro a
    simp only [BooleanExpr.size]
    have := h.state a.1
    have := h.stack k ⟨0, hw⟩ a.2
    omega
  have ht := BooleanExpr.size_lookup_le (fun a : σ × Option Bool => decide (v = f a.1 a.2)) _
    (2 * bound + 1) hi
  have hb : ((sym.read hw k f).state v).size ≤ readBound σ bound := by
    simpa only [read, readBound, Nat.add_assoc] using ht
  exact hb.trans (read_le_operation bound)

theorem pop_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound)
    (hb : 1 ≤ bound) (k : K) : (sym.pop k).Bounded bound := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  dsimp only [pop]
  split_ifs
  · exact h.stack _ _ _
  · exact hb
  · exact h.stack _ _ _

theorem jump_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) (f : σ → Λ) :
    (sym.jump f).Bounded (operationBound σ bound) := by
  refine ⟨?_, fun v => (h.state v).trans (old_le_operation bound),
    fun k i b => (h.stack k i b).trans (old_le_operation bound)⟩
  intro l
  exact (BooleanExpr.size_lookup_le _ _ bound h.state).trans (lookup_le_operation bound)

theorem halt_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) :
    sym.halt.Bounded (bound + 1) :=
  ⟨fun _ => by simp only [halt, BooleanExpr.size]; omega,
    fun v => (h.state v).trans (Nat.le_add_right _ _),
    fun k i b => (h.stack k i b).trans (Nat.le_add_right _ _)⟩

theorem select_bounded (condition : BooleanExpr) (a b : Symbolic K Λ σ width)
    (conditionBound firstBound secondBound : ℕ)
    (hc : condition.size ≤ conditionBound) (ha : a.Bounded firstBound) (hb : b.Bounded secondBound) :
    (select condition a b).Bounded (2 * conditionBound + firstBound + secondBound + 7) := by
  have hh (e f : BooleanExpr) (he : e.size ≤ firstBound) (hf : f.size ≤ secondBound) :
      (BooleanExpr.select condition e f).size ≤ 2 * conditionBound + firstBound + secondBound + 7 := by
    rw [BooleanExpr.size_select]; omega
  exact ⟨fun l => hh _ _ (ha.label l) (hb.label l),
    fun v => hh _ _ (ha.state v) (hb.state v),
    fun k i b => hh _ _ (ha.stack k i b) (hb.stack k i b)⟩

theorem compiled_length_le (sym : Symbolic K Λ σ width) (start bound : ℕ) (h : sym.Bounded bound) :
    (sym.compiled start).1.length ≤ bound * Fintype.card (Slot K Λ σ width) := by
  rw [compiled, BooleanExpr.compileMany_length]
  have hh : ∀ e ∈ sym.formulas, e.size ≤ bound := by
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    generalize (slotEquiv K Λ σ width).symm i = slot
    rcases slot with l | v | ⟨k, i, b⟩
    · exact h.label l
    · exact h.state v
    · exact h.stack k i b
  have sumBound : ∀ es : List BooleanExpr, (∀ e ∈ es, e.size ≤ bound) →
      (es.map BooleanExpr.size).sum ≤ es.length * bound := by
    intro es
    induction es with
    | nil => simp
    | cons e es ih =>
      intro hx
      have he := hx e (by simp)
      have ht := ih (fun a ha => hx a (by simp [ha]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have hl := sumBound sym.formulas hh
  simpa only [formulas_length, Nat.mul_comm] using hl

end Symbolic

theorem auxiliary_bounded (hw : 0 < width) (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) (bound : ℕ) (h : sym.Bounded bound) :
    (auxiliary hw q sym).Bounded (auxiliaryBound q bound) := by
  induction q generalizing sym bound with
  | push k f q ih => exact ih _ _ (sym.push_bounded h k f)
  | peek k f q ih => exact ih _ _ (sym.read_bounded h hw k f)
  | pop k f q ih =>
    exact ih _ _ ((sym.read hw k f).pop_bounded (sym.read_bounded h hw k f)
      (by simp only [Symbolic.operationBound, Symbolic.lookupBound, Symbolic.readBound]; omega) k)
  | load f q ih => exact ih _ _ (sym.load_bounded h f)
  | branch f q r iq ir =>
    exact Symbolic.select_bounded _ _ _ _ _ _ (BooleanExpr.size_lookup_le f sym.state bound h.state)
      (iq _ _ h) (ir _ _ h)
  | goto f => exact sym.jump_bounded h f
  | halt => exact sym.halt_bounded h

theorem transition_bounded (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) (bound : ℕ) (h : sym.Bounded bound) :
    (transition hw program sym).Bounded (transitionBound program bound) := by
  have hh : ∀ l : Option Λ,
      (l.elim sym (fun l => auxiliary hw (program l) sym)).Bounded
        (bound + Finset.univ.sup (fun l => auxiliaryBound (program l) bound)) := by
    intro l
    cases l with
    | none => exact h.mono (Nat.le_add_right _ _)
    | some l =>
      exact (auxiliary_bounded hw (program l) sym bound h).mono
        ((Finset.le_sup (f := fun l => auxiliaryBound (program l) bound) (Finset.mem_univ l)).trans
          (Nat.le_add_left _ _))
  exact ⟨fun l => BooleanExpr.size_multiplex_le _ _ _ _ h.label (fun a => (hh a).label l),
    fun v => BooleanExpr.size_multiplex_le _ _ _ _ h.label (fun a => (hh a).state v),
    fun k i b => BooleanExpr.size_multiplex_le _ _ _ _ h.label (fun a => (hh a).stack k i b)⟩

/-- After rebinding, every new step has constant formula size per configuration slot. -/
theorem compileRun_length_le (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : Symbolic K Λ σ width) (h : sym.Bounded 0) :
    (compileRun hw program ticks start sym).1.length ≤
      ticks * (transitionBound program 0 * Fintype.card (Slot K Λ σ width)) := by
  induction ticks generalizing start sym with
  | zero => simp [compileRun]
  | succ ticks ih =>
    have hf := (transition hw program sym).compiled_length_le start _ (transition_bounded hw program sym 0 h)
    have hr := ih (start + ((transition hw program sym).compiled start).1.length) _
      ((transition hw program sym).rebound_bounded_zero start)
    simp only [compileRun, List.length_append]
    nlinarith

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule37

/- Helper module Solutions.RegevBridgeTM2Initial. -/
section P2MDyadicModule38

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

theorem inputCell_eval (wire : ℕ) (b : Option Bool) (bits : ℕ → Bool) :
    (inputCell wire b).eval bits = decide (b = some (bits wire)) := by
  cases b with
  | none => rfl
  | some b => cases b <;> cases h : bits wire <;> simp [inputCell, BooleanExpr.eval, h]

theorem initial_bounded (input : K) (main : Λ) (initialState : σ) (length width : ℕ) :
    (initial input main initialState length width).Bounded 1 := by
  refine ⟨fun _ => le_rfl, fun _ => le_rfl, ?_⟩
  intro k i b
  dsimp only [initial]
  split_ifs
  · cases b with
    | none => exact le_rfl
    | some b => cases b <;> simp [inputCell, BooleanExpr.size]
  · exact le_rfl

theorem initial_encodes (input : K) (main : Λ) (initialState : σ) (width : ℕ)
    (word : List Bool) (bits : ℕ → Bool)
    (hbits : ∀ i, ∀ hi : i < word.length, bits i = word[i]) :
    Encodes (initial input main initialState word.length width)
      (initialConfiguration input main initialState word) bits := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro k i b
  dsimp only [initial, initialConfiguration]
  by_cases hk : k = input
  · simp only [hk, ↓reduceIte, true_and]
    by_cases hi : i.val < word.length
    · simp only [hi, ↓reduceIte, inputCell_eval, hbits i.val hi, List.getElem?_eq_getElem hi]
    · simp only [hi, ↓reduceIte, BooleanExpr.eval, List.getElem?_eq_none (by omega : word.length ≤ i.val)]
  · simp [hk, BooleanExpr.eval]

theorem initial_size_le (input : K) (main : Λ) (initialState : σ) (word : List Bool) :
    stackSize (initialConfiguration input main initialState word).stk ≤ word.length := by
  apply Finset.sup_le
  intro k hk
  by_cases he : k = input
  · simp [initialConfiguration, he]
  · simp [initialConfiguration, he]

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule38

/- Helper module Solutions.RegevBridgeTM2CodeRegisters. -/
section P2MDyadicModule39

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ α : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

namespace CodeFamily

theorem initialCode_poly [Coding α] (input : K) (main : Λ) (initialState : σ)
    (length : α → ℕ) (hl : Poly length) : (initialCode input main initialState length).IsPoly := by
  refine ⟨fun l => CodePoly.constant _, fun v => CodePoly.constant _, ?_⟩
  intro k b
  have hc : CodePoly (fun x : α × ℕ => inputCell x.2 b) := by
    cases b with
    | none => exact CodePoly.constant false
    | some b => cases b
                · exact (CodePoly.input (show Poly (fun x : α × ℕ => x.2) by fun_prop)).negate
                · exact CodePoly.input (by fun_prop)
  by_cases hk : k = input
  · simp only [initialCode, hk, true_and]
    have hp : Poly (fun x : α × ℕ => decide (x.2 < length x.1)) := by fun_prop
    simpa only [decide_eq_true_eq] using CodePoly.ite hp hc (CodePoly.constant (decide (b=none)))
  · simpa only [initialCode, hk, false_and, ↓reduceIte] using
      (CodePoly.constant (α := α × ℕ) (decide (b=none)))

theorem reboundCode_poly [Coding α] (width : α → ℕ) (refs : α → List ℕ)
    (hw : Poly width) (hr : Poly refs) : (reboundCode (K := K) (Λ := Λ) (σ := σ) width refs).IsPoly := by
  constructor
  · intro l
    apply CodePoly.input
    fun_prop
  · intro v
    apply CodePoly.input
    fun_prop
  · intro k b
    apply CodePoly.input
    fun_prop

end CodeFamily

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule39

/- Helper module Solutions.RegevBridgeBooleanRPNBounds. -/
section P2MDyadicModule40

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

theorem code_length (e : BooleanExpr) : (code e).length ≤ 2*e.size+1 := by
  induction e with
  | input i => simp [code, BooleanExpr.size]
  | constant b => cases b <;> simp [code, BooleanExpr.size]
  | negate a ih => simp only [code, List.length_append, List.length_singleton, BooleanExpr.size]; omega
  | xor a b ia ib | and a b ia ib =>
    simp only [code, List.length_append, List.length_singleton, BooleanExpr.size]; omega

theorem valid_code_bits (e : BooleanExpr) (N : ℕ) (h : e.Valid (2^N)) :
    ∀ t ∈ code e, t.2.bits.length ≤ N := by
  induction e with
  | input i =>
    intro t ht
    simp only [code, List.mem_singleton] at ht
    subst t
    change i.bits.length ≤ N
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr h
  | constant b => cases b <;> simp [code]
  | negate a ih =>
    intro t ht
    simp only [code, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact ih h t ht
    · simp
  | xor a b ia ib | and a b ia ib =>
    intro t ht
    simp only [code, List.mem_append, List.mem_singleton] at ht
    rcases ht with (ht | ht) | rfl
    · exact ia h.1 t ht
    · exact ib h.2 t ht
    · simp

theorem codes_length (es : List BooleanExpr) (C : ℕ) (h : ∀ e ∈ es, e.size ≤ C) :
    (es.flatMap code).length ≤ (2*C+1)*es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := (code_length e).trans (show 2*e.size+1 ≤ 2*C+1 by have := h e (by simp); omega)
    have hh := ih (fun f hf => h f (by simp [hf]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

theorem reverse_operands_bounded {N : ℕ} {s : State} (h : Bounded N s) :
    Bounded N (s.1, s.2.1.reverse, s.2.2) := by
  refine ⟨h.slots, ?_, h.nodes, ?_, h.code⟩
  · simpa only [List.length_reverse] using h.operands
  · intro x hx
    exact h.refs x (List.mem_reverse.mp hx)

theorem clear_operands_bounded {N : ℕ} {s : State} (h : Bounded N s) :
    Bounded N (s.1, [], s.2.2) := ⟨h.slots, Nat.zero_le _, h.nodes, by simp, h.code⟩

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule40

/- Helper module Solutions.RegevBridgeTM2CodeStep. -/
section P2MDyadicModule41

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

theorem registers_poly : (registers (K := K) (Λ := Λ) (σ := σ)).IsPoly :=
  CodeFamily.reboundCode_poly _ _ (by fun_prop) (by fun_prop)

theorem registers_bounded (x : Input) :
    ((registers (K := K) (Λ := Λ) (σ := σ)).restrict x x.1.length).Bounded 0 := by
  exact ⟨fun _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl⟩

theorem registers_valid (x : Input) (N : ℕ) (h : ∀ a ∈ x.2.2.1, a.bits.length ≤ N) :
    ((registers (K := K) (Λ := Λ) (σ := σ)).restrict x x.1.length).Valid (2^N) := by
  have hb : ∀ i : ℕ, ((x.2.2.1[i]?).getD 0) < 2^N := by
    intro i
    have hi := getD_bound x.2.2.1 i N h
    rw [Nat.size_eq_bits_len] at hi
    exact Nat.size_le.mp hi
  exact ⟨fun _ => hb _, fun _ => hb _, fun _ _ _ => hb _⟩

@[fun_prop] theorem tokens_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : Poly (tokens program) :=
  CodeFamily.codes_poly _ (CodeFamily.transitionCode_poly _ (by fun_prop) program _ registers_poly) _ (by fun_prop)

@[fun_prop] theorem step_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : Poly (step program) := by
  unfold step
  fun_prop

theorem tokens_length (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : Input)
    (hw : 0 < x.1.length) : (tokens program x).length ≤ tokenBound program x.1.length := by
  rw [tokens_eq program x hw]
  have hb := transition_bounded hw program _ 0 (registers_bounded (K := K) (Λ := Λ) (σ := σ) x)
  have hh := codes_length (transition hw program (registers.restrict x x.1.length)).formulas
    (transitionBound program 0) (by
      intro e he
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
      rcases (slotEquiv K Λ σ x.1.length).symm i with l | v | ⟨k,i,b⟩
      · exact hb.label l
      · exact hb.state v
      · exact hb.stack k i b)
  simpa only [Symbolic.formulas_length, tokenBound] using hh

theorem tokens_bits (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : Input)
    (hw : 0 < x.1.length) (N : ℕ) (h : ∀ a ∈ x.2.2.1, a.bits.length ≤ N) :
    ∀ t ∈ tokens program x, t.2.bits.length ≤ N := by
  rw [tokens_eq program x hw]
  have hv := transition_valid hw program _ (registers_valid (K := K) (Λ := Λ) (σ := σ) x N h)
  intro t ht
  obtain ⟨e, he, ht⟩ := List.mem_flatMap.mp ht
  exact valid_code_bits e N ((transition hw program (registers.restrict x x.1.length)).formulas_valid hv e he) t ht

theorem step_bounded (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : Input)
    (N : ℕ) (hN : 3 ≤ N) (h : RPN.Bounded N x.2) :
    RPN.Bounded (N+tokenBound program x.1.length) (step program x).2 := by
  unfold step
  split
  · exact h.mono (Nat.le_add_right _ _)
  · rename_i hw
    have hw' : 0 < x.1.length := by
      have hx : x.1 ≠ [] := by simpa only [List.isEmpty_iff] using hw
      exact List.length_pos_iff.mpr hx
    have hb := run_bounded (tokens program x) (clear_operands_bounded h) hN (tokens_bits program x hw' N h.refs)
    exact (reverse_operands_bounded hb).mono (Nat.add_le_add_left (tokens_length program x hw') N)

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule41

/- Helper module Solutions.RegevBridgeTM2CodeLoop. -/
section P2MDyadicModule42

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

theorem iterateCode_bounded (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (fuel : List Unit)
    (x : Input) (N : ℕ) (hN : 3 ≤ N) (h : RPN.Bounded N x.2) :
    RPN.Bounded (N+fuel.length*tokenBound program x.1.length) (iterateCode program fuel x).2 := by
  induction fuel generalizing x N with
  | nil => simpa only [iterateCode, List.foldl_nil, List.length_nil, Nat.zero_mul, Nat.add_zero] using h
  | cons u fuel ih =>
    have hs := step_bounded program x N hN h
    have hh := ih (step program x) (N+tokenBound program x.1.length) (by omega) hs
    simpa only [iterateCode, List.foldl_cons, List.length_cons, step_width, Nat.add_mul,
      Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem tokenBound_le (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (width : ℕ) :
    tokenBound program width ≤ tokenRate program*(width+1) := by
  unfold tokenBound tokenRate
  rw [slot_count]
  have h : Fintype.card Λ+1+Fintype.card σ+Fintype.card K*width*3 ≤
      (Fintype.card Λ+1+Fintype.card σ+Fintype.card K*3)*(width+1) := by nlinarith
  have hh := Nat.mul_le_mul_left (2*transitionBound program 0+1) h
  simpa only [Nat.mul_assoc] using hh

theorem iterateCode_partial_bound (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (fuel : List Unit) (x : Input) (pre suf : List Unit) (he : fuel=pre++suf) :
    (enc (iterateCode program pre x)).length ≤ (loopBound program).eval (enc (fuel,x)).length := by
  let L := (enc (fuel,x)).length
  have heL : L = 2*fuel.length+1+2*x.1.length+1+(enc x.2).length := by
    change (encodePair (enc : List Unit → List Bool) (encodePair enc enc) (fuel,x)).length = _
    simp only [encodePair_length, encodedUnit_length]
    omega
  have hw : x.1.length ≤ L := by omega
  have hp : pre.length ≤ L := by have hh := congrArg List.length he; simp only [List.length_append] at hh; omega
  have hs := (bounded_of_encoding x.2).mono (show (enc x.2).length ≤ L+3 by omega)
  have hb := iterateCode_bounded program pre x (L+3) (by omega) hs
  have ht := (tokenBound_le program x.1.length).trans
    (Nat.mul_le_mul_left (tokenRate program) (Nat.add_le_add_right hw 1))
  have hm : pre.length * tokenBound program x.1.length ≤ L*tokenRate program*(L+1) := by
    exact (Nat.mul_le_mul hp ht).trans_eq (Nat.mul_assoc _ _ _).symm
  have hb' := hb.mono (Nat.add_le_add_left hm (L+3))
  have hh := encoding_bound hb'
  have hwidth := iterateCode_width program pre x
  have henc : (enc (iterateCode program pre x)).length = 2*x.1.length+1+(enc (iterateCode program pre x).2).length := by
    change (encodePair (enc : List Unit → List Bool) enc (iterateCode program pre x)).length = _
    rw [encodePair_length, encodedUnit_length, hwidth]
  simp only [loopBound, eval_add, eval_mul, eval_ofNat, eval_X, eval_one, eval_pow, eval_C]
  change _ ≤ 2*L+1+20*(L+3+L*tokenRate program*(L+1)+1)^2
  omega

@[fun_prop] theorem iterateCode_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) :
    Poly (fun x : List Unit × Input => iterateCode program x.1 x.2) := by
  have hs : Poly (fun x : Input × Unit => step program x.1) := by fun_prop
  apply Automatic.Poly.of_program
  exact hs.program.listFold () (loopBound program) (by
    intro fuel x pre suf he
    change (enc (iterateCode program pre x)).length ≤ (loopBound program).eval (enc (fuel,x)).length
    exact iterateCode_partial_bound program fuel x pre suf he)

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule42

/- Helper module Solutions.RegevBridgeTM2MachineProgram. -/
section P2MDyadicModule43

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

theorem Encodes.get {sym : Symbolic K Λ σ width} {cfg : Configuration K Λ σ}
    {bits : ℕ → Bool} (h : Encodes sym cfg bits) (i : Slot K Λ σ width) :
    (sym.get i).eval bits = configurationBit cfg i := by
  rcases i with l | v | ⟨k, i, b⟩
  · exact h.label l
  · exact h.state v
  · exact h.stack k i b

theorem compileRun_rebound_bounded (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : Symbolic K Λ σ width) (h : sym.Bounded 0) :
    (compileRun hw program ticks start sym).2.Bounded 0 := by
  induction ticks generalizing start sym with
  | zero => exact h
  | succ ticks ih => exact ih _ _ ((transition hw program sym).rebound_bounded_zero start)

theorem machineProgram_length_le (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks length : ℕ) :
    (machineProgram hw program input main initialState ticks length).ops.length ≤
      (1 + ticks * transitionBound program 0) * Fintype.card (Slot K Λ σ width) := by
  let init := initial input main initialState length width
  have hi : init.Bounded 1 := initial_bounded input main initialState length width
  have hp := init.compiled_length_le length 1 hi
  have hm := compileRun_length_le hw program ticks (length + (init.compiled length).1.length) _
    (init.rebound_bounded_zero length)
  have hz := compileRun_rebound_bounded hw program ticks (length + (init.compiled length).1.length) _
    (init.rebound_bounded_zero length)
  let middle := compileRun hw program ticks (length + (init.compiled length).1.length) (init.rebound length)
  have he := middle.2.compiled_length_le
    (length + (init.compiled length).1.length + middle.1.length) 0 hz
  change ((init.compiled length).1 ++ middle.1 ++
    (middle.2.compiled (length + (init.compiled length).1.length + middle.1.length)).1).length ≤ _
  simp only [List.length_append]
  nlinarith

/-- The whole generated straight-line program computes every field of the budgeted machine execution. -/
theorem machineProgram_semantics (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks : ℕ)
    (word : List Bool) (bits : ℕ → Bool)
    (hbits : ∀ i, ∀ hi : i < word.length, bits i = word[i])
    (hsize : word.length + programPushBound program * ticks ≤ width) (i : Slot K Λ σ width) :
    BooleanProgram.run word.length (machineProgram hw program input main initialState ticks word.length).ops bits
      ((machineProgram hw program input main initialState ticks word.length).output i) =
      configurationBit ((stickyStep program)^[ticks] (initialConfiguration input main initialState word)) i := by
  let init := initial input main initialState word.length width
  have hi : init.Valid word.length := initial_valid input main initialState word.length width
  have he : Encodes init (initialConfiguration input main initialState word) bits :=
    initial_encodes input main initialState width word bits hbits
  have hp := init.rebound_encodes word.length hi _ bits he
  have hr := compileRun_encodes hw program ticks _ _ _ _
    (init.rebound_valid word.length hi) hp
    ((Nat.add_le_add_right (initial_size_le input main initialState word) _).trans hsize)
  have hv := (compileRun_valid hw program ticks _ _ (init.rebound_valid word.length hi)).2
  let middle := compileRun hw program ticks (word.length + (init.compiled word.length).1.length)
    (init.rebound word.length)
  have ho := middle.2.output_eval _ hv
    (BooleanProgram.run (word.length + (init.compiled word.length).1.length) middle.1
      (BooleanProgram.run word.length (init.compiled word.length).1 bits)) i
  rw [hr.get i] at ho
  simpa only [machineProgram, BooleanProgram.run_append, List.length_append, Nat.add_assoc, init, middle] using ho

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule43

/- Helper module Solutions.RegevBridgeTM2CodeGenerate. -/
section P2MDyadicModule44

set_option autoImplicit false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

@[fun_prop] theorem initialResult_poly (input : K) (main : Λ) (initialState : σ) :
    Poly (initialResult input main initialState) :=
  CodeFamily.compile_poly _ (CodeFamily.initialCode_poly _ _ _ _ (by fun_prop)) _ _ (by fun_prop) (by fun_prop)

@[fun_prop] theorem initialInput_poly (input : K) (main : Λ) (initialState : σ) :
    Poly (initialInput input main initialState) := by
  unfold initialInput
  fun_prop

@[fun_prop] theorem generate_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) : Poly (generate program input main initialState) := by
  unfold generate
  fun_prop

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule44

/- Helper module Solutions.RegevBridgeBooleanNodeSerialization. -/
section P2MDyadicModule45

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem boundedNat_poly : Poly (fun x : List Unit × ℕ => boundedNat x.1 x.2) := by
  unfold boundedNat
  fun_prop

@[fun_prop] theorem instructionWord_poly :
    Poly (fun x : List Unit × (ℕ × Node) => instructionWord x.1 x.2.1 x.2.2) := by
  unfold instructionWord
  fun_prop

@[fun_prop] theorem instructionWords_poly :
    Poly (fun x : List Unit × (ℕ × List Node) => instructionWords x.1 x.2.1 x.2.2) := by
  unfold instructionWords
  apply Automatic.Poly.list_map
  · fun_prop
  · exact Automatic.Poly.comp (f := fun xs : List Node => List.range xs.length)
      (g := fun x : List Unit × (ℕ × List Node) => x.2.2) Automatic.Poly.list_indices (by fun_prop)

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule45

/- Helper module Solutions.AdvantageBridgeDisjointCircuit. -/
section P2MDyadicModule46

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

private theorem leftRegister_update_left {n m : ℕ} (state : Bits (n+m)) (wire : Fin n) (bit : Bool) :
    leftRegister (Function.update state (Fin.castAdd m wire) bit)=Function.update (leftRegister state) wire bit := by
  funext index
  by_cases h : index=wire
  · subst index
    simp [leftRegister]
  · have he : Fin.castAdd m index ≠ Fin.castAdd m wire := fun hh => h (Fin.ext (congrArg (fun k : Fin (n+m) => k.val) hh))
    simp [leftRegister,Function.update_of_ne h,Function.update_of_ne he]

private theorem rightRegister_update_left {n m : ℕ} (state : Bits (n+m)) (wire : Fin n) (bit : Bool) :
    rightRegister (Function.update state (Fin.castAdd m wire) bit)=rightRegister state := by
  funext index
  have he : Fin.natAdd n index ≠ Fin.castAdd m wire := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    have hi := wire.isLt
    omega
  simp [rightRegister,Function.update_of_ne he]

private theorem leftRegister_update_right {n m : ℕ} (state : Bits (n+m)) (wire : Fin m) (bit : Bool) :
    leftRegister (Function.update state (Fin.natAdd n wire) bit)=leftRegister state := by
  funext index
  have he : Fin.castAdd m index ≠ Fin.natAdd n wire := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    have hi := index.isLt
    omega
  simp [leftRegister,Function.update_of_ne he]

private theorem rightRegister_update_right {n m : ℕ} (state : Bits (n+m)) (wire : Fin m) (bit : Bool) :
    rightRegister (Function.update state (Fin.natAdd n wire) bit)=Function.update (rightRegister state) wire bit := by
  funext index
  by_cases h : index=wire
  · subst index
    simp [rightRegister]
  · have he : Fin.natAdd n index ≠ Fin.natAdd n wire := by
      intro hh
      exact h (Fin.ext (Nat.add_left_cancel (congrArg Fin.val hh)))
    simp [rightRegister,Function.update_of_ne h,Function.update_of_ne he]

private theorem apply1_left_tensor {n m : ℕ} (matrix : Matrix Bool Bool ℂ) (wire : Fin n)
    (first : QState n) (second : QState m) :
    apply1 matrix (Fin.castAdd m wire) (tensorState first second)=tensorState (apply1 matrix wire first) second := by
  funext state
  simp only [apply1,tensorState,leftRegister_update_left,rightRegister_update_left]
  change (∑ bit,matrix (leftRegister state wire) bit*
    (first (Function.update (leftRegister state) wire bit)*second (rightRegister state))) =
      (∑ bit,matrix (leftRegister state wire) bit*first (Function.update (leftRegister state) wire bit))*
        second (rightRegister state)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro bit _
  ring

private theorem apply1_right_tensor {n m : ℕ} (matrix : Matrix Bool Bool ℂ) (wire : Fin m)
    (first : QState n) (second : QState m) :
    apply1 matrix (Fin.natAdd n wire) (tensorState first second)=tensorState first (apply1 matrix wire second) := by
  funext state
  simp only [apply1,tensorState,leftRegister_update_right,rightRegister_update_right]
  change (∑ bit,matrix (rightRegister state wire) bit*
    (first (leftRegister state)*second (Function.update (rightRegister state) wire bit))) =
      first (leftRegister state)*
        (∑ bit,matrix (rightRegister state wire) bit*second (Function.update (rightRegister state) wire bit))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bit _
  ring

/-- All five actual Clifford+T gate constructors act on their designated
left register and leave the other register untouched. -/
theorem leftInstruction_tensor {n m : ℕ} (gate : Instr n) (first : QState n) (second : QState m) :
    (leftInstruction gate).apply (tensorState first second)=tensorState (gate.apply first) second := by
  cases gate with
  | h wire => exact apply1_left_tensor hMat wire first second
  | s wire => exact apply1_left_tensor sMat wire first second
  | t wire => exact apply1_left_tensor tMat wire first second
  | x wire => exact apply1_left_tensor xMat wire first second
  | cnot control target hct =>
    funext state
    simp only [leftInstruction,Instr.apply,cnotState,tensorState,leftRegister_update_left,rightRegister_update_left]
    rfl

/-- The same exact gate semantics for the right physical register. -/
theorem rightInstruction_tensor {n m : ℕ} (gate : Instr m) (first : QState n) (second : QState m) :
    (rightInstruction gate).apply (tensorState first second)=tensorState first (gate.apply second) := by
  cases gate with
  | h wire => exact apply1_right_tensor hMat wire first second
  | s wire => exact apply1_right_tensor sMat wire first second
  | t wire => exact apply1_right_tensor tMat wire first second
  | x wire => exact apply1_right_tensor xMat wire first second
  | cnot control target hct =>
    funext state
    simp only [rightInstruction,Instr.apply,cnotState,tensorState,leftRegister_update_right,rightRegister_update_right]
    rfl

private theorem leftLayer_tensor {n m : ℕ} (layer : List (Instr n)) (first : QState n) (second : QState m) :
    runLayer (layer.map leftInstruction) (tensorState first second)=tensorState (runLayer layer first) second := by
  induction layer generalizing first with
  | nil => rfl
  | cons gate layer ih =>
    simp only [List.map_cons,runLayer,List.foldl_cons]
    rw [leftInstruction_tensor]
    exact ih (gate.apply first)

private theorem rightLayer_tensor {n m : ℕ} (layer : List (Instr m)) (first : QState n) (second : QState m) :
    runLayer (layer.map rightInstruction) (tensorState first second)=tensorState first (runLayer layer second) := by
  induction layer generalizing second with
  | nil => rfl
  | cons gate layer ih =>
    simp only [List.map_cons,runLayer,List.foldl_cons]
    rw [rightInstruction_tensor]
    exact ih (gate.apply second)

theorem leftCircuit_tensor {n m : ℕ} (circuit : Layered n) (first : QState n) (second : QState m) :
    runLayered (leftCircuit circuit) (tensorState first second)=tensorState (runLayered circuit first) second := by
  induction circuit generalizing first with
  | nil => rfl
  | cons layer circuit ih =>
    simp only [leftCircuit,List.map_cons,runLayered,List.foldl_cons]
    rw [leftLayer_tensor]
    exact ih (runLayer layer first)

theorem rightCircuit_tensor {n m : ℕ} (circuit : Layered m) (first : QState n) (second : QState m) :
    runLayered (rightCircuit circuit) (tensorState first second)=tensorState first (runLayered circuit second) := by
  induction circuit generalizing second with
  | nil => rfl
  | cons layer circuit ih =>
    simp only [rightCircuit,List.map_cons,runLayered,List.foldl_cons]
    rw [rightLayer_tensor]
    exact ih (runLayer layer second)

/-- Two real circuits on disjoint registers have exactly their product action. -/
theorem disjointCircuits_tensor {n m : ℕ} (left : Layered n) (right : Layered m)
    (first : QState n) (second : QState m) :
    runLayered (leftCircuit left++rightCircuit right) (tensorState first second)=
      tensorState (runLayered left first) (runLayered right second) := by
  rw [runLayered,List.foldl_append]
  change runLayered (rightCircuit right) (runLayered (leftCircuit left) (tensorState first second)) = _
  rw [leftCircuit_tensor,rightCircuit_tensor]

/-- An unused normalized register contributes exactly one to the selected
left output probability, even after its own independent quantum circuit. -/
theorem tensorState_left_acceptance {n m : ℕ} (first : QState n) (second : QState m) (out : Fin n)
    (hsecond : ∑ state,‖second state‖^2=1) :
    (∑ state : Bits (n+m),if state (Fin.castAdd m out) then ‖tensorState first second state‖^2 else 0)=
      ∑ state : Bits n,if state out then ‖first state‖^2 else 0 := by
  change (∑ state : Bits (n+m),if leftRegister state out then
    ‖first (leftRegister state)*second (rightRegister state)‖^2 else 0)=_
  rw [sum_registers (fun left right => if left out then ‖first left*second right‖^2 else 0)]
  have hpoint (left : Bits n) (right : Bits m) :
      (if left out then ‖first left*second right‖^2 else 0)=
        (if left out then ‖first left‖^2 else 0)*‖second right‖^2 := by
    cases left out <;> simp [norm_mul,mul_pow]
  simp only [hpoint,←Finset.mul_sum,hsecond,mul_one]

private theorem left_support_disjoint {n m : ℕ} (first second : Instr n)
    (h : Disjoint first.support second.support) :
    Disjoint (leftInstruction (m := m) first).support (leftInstruction second).support := by
  rw [leftInstruction_support,leftInstruction_support]
  apply Finset.disjoint_left.mpr
  intro index hi hj
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hj
  have hab : b=a := Fin.ext (congrArg (fun k : Fin (n+m) => k.val) he)
  subst b
  exact Finset.disjoint_left.mp h ha hb

private theorem right_support_disjoint {n m : ℕ} (first second : Instr m)
    (h : Disjoint first.support second.support) :
    Disjoint (rightInstruction (n := n) first).support (rightInstruction second).support := by
  rw [rightInstruction_support,rightInstruction_support]
  apply Finset.disjoint_left.mpr
  intro index hi hj
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hj
  have hab : b=a := Fin.ext (Nat.add_left_cancel (congrArg Fin.val he))
  subst b
  exact Finset.disjoint_left.mp h ha hb

theorem leftLayer_ok {n m : ℕ} (layer : List (Instr n)) (h : LayerOk layer) :
    LayerOk (layer.map (leftInstruction (m := m))) := by
  unfold LayerOk at h ⊢
  rw [List.pairwise_map]
  exact h.imp (fun hab => left_support_disjoint _ _ hab)

theorem rightLayer_ok {n m : ℕ} (layer : List (Instr m)) (h : LayerOk layer) :
    LayerOk (layer.map (rightInstruction (n := n))) := by
  unfold LayerOk at h ⊢
  rw [List.pairwise_map]
  exact h.imp (fun hab => right_support_disjoint _ _ hab)

theorem leftCircuit_wellFormed {n m : ℕ} (circuit : Layered n)
    (h : ∀ layer ∈ circuit,LayerOk layer) : ∀ layer ∈ leftCircuit (m := m) circuit,LayerOk layer := by
  intro layer hl
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hl
  exact leftLayer_ok original (h original ho)

theorem rightCircuit_wellFormed {n m : ℕ} (circuit : Layered m)
    (h : ∀ layer ∈ circuit,LayerOk layer) : ∀ layer ∈ rightCircuit (n := n) circuit,LayerOk layer := by
  intro layer hl
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hl
  exact rightLayer_ok original (h original ho)

/-- The symmetric selected-output identity. -/
theorem tensorState_right_acceptance {n m : ℕ} (first : QState n) (second : QState m) (out : Fin m)
    (hfirst : ∑ state,‖first state‖^2=1) :
    (∑ state : Bits (n+m),if state (Fin.natAdd n out) then ‖tensorState first second state‖^2 else 0)=
      ∑ state : Bits m,if state out then ‖second state‖^2 else 0 := by
  change (∑ state : Bits (n+m),if rightRegister state out then
    ‖first (leftRegister state)*second (rightRegister state)‖^2 else 0)=_
  rw [sum_registers (fun left right => if right out then ‖first left*second right‖^2 else 0)]
  have hpoint (left : Bits n) (right : Bits m) :
      (if right out then ‖first left*second right‖^2 else 0)=
        ‖first left‖^2*(if right out then ‖second right‖^2 else 0) := by
    cases right out <;> simp [norm_mul,mul_pow]
  simp only [hpoint,←Finset.mul_sum,←Finset.sum_mul,hfirst,one_mul]

/-- Running every unselected circuit block has no effect on the selected
left block's exact acceptance probability. -/
theorem disjointCircuits_left_acceptance {n m : ℕ} (left : Layered n) (right : Layered m)
    (first : QState n) (second : QState m) (out : Fin n)
    (hsecond : ∑ state,‖second state‖^2=1) :
    (∑ state : Bits (n+m),if state (Fin.castAdd m out) then
      ‖runLayered (leftCircuit left++rightCircuit right) (tensorState first second) state‖^2 else 0)=
      ∑ state : Bits n,if state out then ‖runLayered left first state‖^2 else 0 := by
  rw [disjointCircuits_tensor]
  apply tensorState_left_acceptance
  have hnorm : (∑ state,‖runLayered right second state‖^2)=∑ state,‖second state‖^2 := by
    simpa only [Complex.normSq_eq_norm_sq] using runLayered_mass right second
  exact hnorm.trans hsecond

/-- The analogous real-circuit guarantee when selecting a block in the right register. -/
theorem disjointCircuits_right_acceptance {n m : ℕ} (left : Layered n) (right : Layered m)
    (first : QState n) (second : QState m) (out : Fin m)
    (hfirst : ∑ state,‖first state‖^2=1) :
    (∑ state : Bits (n+m),if state (Fin.natAdd n out) then
      ‖runLayered (leftCircuit left++rightCircuit right) (tensorState first second) state‖^2 else 0)=
      ∑ state : Bits m,if state out then ‖runLayered right second state‖^2 else 0 := by
  rw [disjointCircuits_tensor]
  apply tensorState_right_acceptance
  have hnorm : (∑ state,‖runLayered left first state‖^2)=∑ state,‖first state‖^2 := by
    simpa only [Complex.normSq_eq_norm_sq] using runLayered_mass left first
  exact hnorm.trans hfirst

/-- A real compiled reversible circuit pulls each output event back along
its exact classical permutation, for arbitrary superpositions and garbage. -/
theorem reversibleCircuit_event_probability {n : ℕ} (gates : List (ReversibleGate n))
    (state : QState n) (event : Bits n → Bool) :
    (∑ output : Bits n,if event output then
      ‖runLayered (compileReversible gates) state output‖^2 else 0)=
      ∑ input : Bits n,if event (reversibleAction gates input) then ‖state input‖^2 else 0 := by
  rw [compileReversible_apply]
  have h := (reversibleAction gates).sum_comp (fun output : Bits n =>
    if event output then ‖state ((reversibleAction gates).symm output)‖^2 else 0)
  simpa only [Equiv.symm_apply_apply] using h.symm

/-- Fresh Boolean output selection has its exact classical event semantics
on quantum states supported on zero scratch inputs. -/
theorem booleanCircuit_event_probability {n : ℕ} (gates : List (BooleanGate n))
    (hf : BooleanFresh gates) (state : QState n)
    (hz : ∀ input,state input ≠ 0 → ∀ gate ∈ gates,input gate.target=false)
    (event : Bits n → Bool) :
    (∑ output : Bits n,if event output then
      ‖runLayered (compileReversible (booleanToReversible gates)) state output‖^2 else 0)=
      ∑ input : Bits n,if event (booleanRun gates input) then ‖state input‖^2 else 0 := by
  rw [reversibleCircuit_event_probability]
  apply Finset.sum_congr rfl
  intro input _
  by_cases he : state input=0
  · simp [he]
  · rw [booleanToReversible_action gates hf input (hz input he)]

end InfoLossLAR.WorstCase

end P2MDyadicModule46

/- Helper module Solutions.AdvantageBridgeCircuitBundle. -/
section P2MDyadicModule47

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

/-- The selected physical block has exactly its own acceptance probability,
although all blocks of different sizes actually run on disjoint registers. -/
theorem bundle_selected_probability (blocks : List QuantumBlock) (index : Fin blocks.length) :
    (∑ state : Bits (bundleWidth blocks),if state (bundleOutput blocks index) then
      ‖runLayered (bundleCircuit blocks) (bundleState blocks) state‖^2 else 0)=
      (blocks.get index).probability := by
  induction blocks with
  | nil => exact Fin.elim0 index
  | cons block blocks ih =>
    refine Fin.cases ?_ (fun tail => ?_) index
    · change (∑ state : Bits (block.wires+bundleWidth blocks),if state (Fin.castAdd (bundleWidth blocks) block.out) then
        ‖runLayered (leftCircuit block.circuit++rightCircuit (bundleCircuit blocks))
          (tensorState block.input (bundleState blocks)) state‖^2 else 0)=block.probability
      exact disjointCircuits_left_acceptance block.circuit (bundleCircuit blocks)
        block.input (bundleState blocks) block.out (bundleState_mass blocks)
    · change (∑ state : Bits (block.wires+bundleWidth blocks),if state (Fin.natAdd block.wires (bundleOutput blocks tail)) then
        ‖runLayered (leftCircuit block.circuit++rightCircuit (bundleCircuit blocks))
          (tensorState block.input (bundleState blocks)) state‖^2 else 0)=(blocks.get tail).probability
      rw [disjointCircuits_right_acceptance block.circuit (bundleCircuit blocks)
        block.input (bundleState blocks) (bundleOutput blocks tail) block.normalized]
      exact ih tail

theorem bundleCircuit_wellFormed (blocks : List QuantumBlock)
    (h : ∀ block ∈ blocks,∀ layer ∈ block.circuit,LayerOk layer) :
    ∀ layer ∈ bundleCircuit blocks,LayerOk layer := by
  induction blocks with
  | nil => simp [bundleCircuit]
  | cons block blocks ih =>
    intro layer hl
    rcases List.mem_append.mp hl with hl|hl
    · exact leftCircuit_wellFormed block.circuit (h block (by simp)) layer hl
    · exact rightCircuit_wellFormed (bundleCircuit blocks)
        (ih (fun b hb => h b (by simp [hb]))) layer hl

theorem bundleCircuit_depth (blocks : List QuantumBlock) :
    depth (bundleCircuit blocks)=(blocks.map (fun block => depth block.circuit)).sum := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    change depth (leftCircuit block.circuit++rightCircuit (bundleCircuit blocks)) = _
    have hd {n : ℕ} (first second : Layered n) : depth (first++second)=depth first+depth second := List.length_append
    rw [hd,leftCircuit_depth,rightCircuit_depth,ih]
    rfl

theorem familyBlock_probability (D : Family) (word : Str) :
    (familyBlock D word.length (toBits word)).probability=acceptProb D word := rfl

theorem queryBlocks_width_independent (D : Family) (maximum : ℕ) (first second : Str) :
    bundleWidth (queryBlocks D maximum first)=bundleWidth (queryBlocks D maximum second) := by
  simp only [bundleWidth_sum,queryBlocks,List.map_ofFn,familyBlock,Function.comp_def]

/-- A circuit bundle for all possible lengths has the exact output probability
of D at the actual query length. -/
theorem queryBlocks_selected_probability (D : Family) (maximum : ℕ) (query : Str)
    (hlength : query.length ≤ maximum) :
    let index : Fin (queryBlocks D maximum query).length := ⟨query.length,by
      simp only [queryBlocks,List.length_ofFn]
      omega⟩
    (∑ state : Bits (bundleWidth (queryBlocks D maximum query)),
      if state (bundleOutput (queryBlocks D maximum query) index) then
        ‖runLayered (bundleCircuit (queryBlocks D maximum query))
          (bundleState (queryBlocks D maximum query)) state‖^2 else 0)=acceptProb D query := by
  dsimp only
  rw [bundle_selected_probability]
  simp only [queryBlocks,List.get_eq_getElem,List.getElem_ofFn]
  change (familyBlock D query.length (fun index => (query[index.val]?).getD false)).probability=acceptProb D query
  have hbits : (fun index : Fin query.length => (query[index.val]?).getD false)=toBits query := by
    funext index
    simp [toBits,index.isLt]
  rw [hbits,familyBlock_probability]

theorem queryBlocks_wellFormed (D : Family) (hD : WellFormed D) (maximum : ℕ) (query : Str) :
    ∀ layer ∈ bundleCircuit (queryBlocks D maximum query),LayerOk layer := by
  apply bundleCircuit_wellFormed
  intro block hb
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hb
  exact hD index.val

/-- The real many-length circuit has polynomial depth whenever D does. -/
theorem queryBlocks_depth_le (D : Family) (p : Polynomial ℕ)
    (hdepth : ∀ length,depth (D.circ length) ≤ p.eval length) (maximum : ℕ) (query : Str) :
    depth (bundleCircuit (queryBlocks D maximum query)) ≤ (maximum+1)*p.eval maximum := by
  rw [bundleCircuit_depth]
  simp only [queryBlocks,List.map_ofFn,List.sum_ofFn,familyBlock]
  calc
    (∑ index : Fin (maximum+1),depth (D.circ index.val)) ≤ ∑ _ : Fin (maximum+1),p.eval maximum := by
      apply Finset.sum_le_sum
      intro index _
      exact (hdepth index.val).trans (OAI.MetricKMedian.Binary.polynomial_eval_mono p (b := maximum) (by omega))
    _ = _ := by simp

theorem queryBlocks_width_le (D : Family) (p : Polynomial ℕ)
    (hanc : ∀ length,D.anc length ≤ p.eval length) (maximum : ℕ) (query : Str) :
    bundleWidth (queryBlocks D maximum query) ≤ (maximum+1)*(maximum+p.eval maximum+1) := by
  rw [bundleWidth_sum]
  simp only [queryBlocks,List.map_ofFn,List.sum_ofFn,familyBlock]
  calc
    (∑ index : Fin (maximum+1),(index.val+(D.anc index.val+1))) ≤
        ∑ _ : Fin (maximum+1),(maximum+p.eval maximum+1) := by
      apply Finset.sum_le_sum
      intro index _
      have h := (hanc index.val).trans (OAI.MetricKMedian.Binary.polynomial_eval_mono p (b := maximum) (by omega))
      have hi := index.isLt
      omega
    _ = _ := by simp

theorem bundlePhysical_fold (blocks : List QuantumBlock) :
    bundlePhysical blocks=(blocks.map (fun block => (⟨block.wires,block.circuit⟩ : Σ wires : ℕ,Layered wires))).foldr
      appendPhysical ⟨0,[]⟩ := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    change appendPhysical ⟨block.wires,block.circuit⟩ (bundlePhysical blocks)=_
    rw [List.map_cons,List.foldr_cons,ih]

/-- The actual physical circuit for all candidate lengths is independent
of the query contents, including all its qubit counts and wire offsets. -/
theorem queryBlocks_physical_independent (D : Family) (maximum : ℕ) (first second : Str) :
    bundlePhysical (queryBlocks D maximum first)=bundlePhysical (queryBlocks D maximum second) := by
  rw [bundlePhysical_fold,bundlePhysical_fold]
  have h : (queryBlocks D maximum first).map
      (fun block => (⟨block.wires,block.circuit⟩ : Σ wires : ℕ,Layered wires))=
      (queryBlocks D maximum second).map
      (fun block => (⟨block.wires,block.circuit⟩ : Σ wires : ℕ,Layered wires)) := by
    simp only [queryBlocks,List.map_ofFn,familyBlock,Function.comp_def]
  rw [h]

end InfoLossLAR.WorstCase

end P2MDyadicModule47

/- Helper module Solutions.AdvantageBridgeQuantumCoins. -/
section P2MDyadicModule48

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

theorem coinZero_mass (count : ℕ) : (∑ state,‖coinZero count state‖^2)=(1 : ℝ) := by
  classical
  rw [Finset.sum_eq_single (fun _ : Fin count => false)]
  · simp [coinZero]
  · intro state _ hne
    simp [coinZero,hne]
  · simp

theorem coinZero_tensor (first second : ℕ) : coinZero (first+second)=tensorState (coinZero first) (coinZero second) := by
  funext state
  have hzero : state=(fun _ => false) ↔ leftRegister state=(fun _ => false) ∧ rightRegister state=(fun _ => false) := by
    constructor
    · rintro rfl
      exact ⟨rfl,rfl⟩
    · rintro ⟨hl,hr⟩
      funext index
      refine Fin.addCases ?_ ?_ index
      · intro i
        exact congrArg (fun word => word i) hl
      · intro i
        exact congrArg (fun word => word i) hr
  by_cases hl : leftRegister state=(fun _ => false)
  · by_cases hr : rightRegister state=(fun _ => false)
    · change (if state=(fun _ => false) then (1 : ℂ) else 0)=
        (if leftRegister state=(fun _ => false) then 1 else 0)*
          (if rightRegister state=(fun _ => false) then 1 else 0)
      rw [if_pos (hzero.mpr ⟨hl,hr⟩),if_pos hl,if_pos hr,mul_one]
    · have hs : state ≠ (fun _ => false) := fun h => hr (hzero.mp h).2
      simp [coinZero,tensorState,hl,hr,hs]
  · have hs : state ≠ (fun _ => false) := fun h => hl (hzero.mp h).1
    simp [coinZero,tensorState,hl,hs]

private theorem one_coin_uniform : runLayered [[.h (0 : Fin 1)]] (coinZero 1)=
    (fun _ => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) := by
  funext state
  have hf : Function.update state (0 : Fin 1) false=(fun _ => false) := by
    funext index
    have hi : index=0 := Subsingleton.elim _ _
    subst index
    simp
  have ht : Function.update state (0 : Fin 1) true ≠ (fun _ => false) := by
    intro h
    have hh := congrArg (fun word => word 0) h
    simp at hh
  simp only [runLayered,runLayer,List.foldl_cons,List.foldl_nil,Instr.apply,apply1,Fintype.sum_bool]
  simp [coinZero,hf,ht,hMat]

/-- The actual coin preparation circuit has uniform positive amplitudes,
not only the correct total norm. -/
theorem coinCircuit_uniform (count : ℕ) : runLayered (coinCircuit count) (coinZero count)=
    (fun _ => coinAmplitude count) := by
  induction count with
  | zero =>
    funext state
    have hs : state=(fun _ : Fin 0 => false) := Subsingleton.elim _ _
    simp [coinCircuit,runLayered,coinZero,coinAmplitude,hs]
  | succ count ih =>
    rw [coinCircuit,coinZero_tensor count 1,disjointCircuits_tensor,ih,one_coin_uniform]
    funext state
    exact (pow_succ _ count).symm

theorem coinCircuit_wellFormed (count : ℕ) : ∀ layer ∈ coinCircuit count,LayerOk layer := by
  rw [coinCircuit_direct]
  intro layer hl
  obtain ⟨wire,rfl⟩ := List.mem_ofFn.mp hl
  exact List.pairwise_singleton _ _

/-- Each actual Hadamard output has precisely uniform Boolean point mass. -/
theorem coinAmplitude_mass (count : ℕ) : ‖coinAmplitude count‖^2=(Fintype.card (Bits count) : ℝ)⁻¹ := by
  have h := runLayered_mass (coinCircuit count) (coinZero count)
  simp only [coinCircuit_uniform,Complex.normSq_eq_norm_sq] at h
  rw [coinZero_mass] at h
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  have hc : (Fintype.card (Bits count) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply (mul_left_cancel₀ hc)
  rw [h,mul_inv_cancel₀ hc]

section Description

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem coinCircuitDescription_poly : Poly coinCircuitDescription := by
  have hgate : Poly (fun input : Str × ℕ =>
      serializeWords [encNat 0++lengthToken (input.1.take input.2)]) := by
    have ht : Poly (fun input : Str × ℕ => input.1.take input.2) := parser_take_poly
    fun_prop
  unfold coinCircuitDescription
  exact Poly.comp serializeWords_poly (Poly.list_map hgate Poly.list_indices)

/-- The real TM2 serializer emits exactly the actual Hadamard circuit's
published encCirc representation. -/
theorem coinCircuitDescription_correct (xs : Str) :
    coinCircuitDescription xs=encCirc (coinCircuit xs.length) := by
  rw [coinCircuit_direct]
  unfold coinCircuitDescription encCirc
  rw [List.map_ofFn,serializeWords_eq]
  apply congrArg encStr
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    have hi : index<xs.length := by simpa using hleft
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,serializeWords_eq,
      lengthToken_eq,List.length_take,Nat.min_eq_left hi.le,Function.comp_def,encLayer,encInstr,
      List.map_cons,List.map_nil]

end Description

end InfoLossLAR.WorstCase

end P2MDyadicModule48

/- Helper module Solutions.AdvantageBridgeCoinPreparation. -/
section P2MDyadicModule49

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

private theorem append_registers_iff {n m : ℕ} (state : Bits (n+m)) (left : Bits n) (right : Bits m) :
    state=Fin.append left right ↔ leftRegister state=left ∧ rightRegister state=right := by
  constructor
  · rintro rfl
    exact ⟨by funext i; simp [leftRegister],by funext i; simp [rightRegister]⟩
  · rintro ⟨hl,hr⟩
    funext index
    refine Fin.addCases ?_ ?_ index
    · intro i
      simpa only [Fin.append_left,leftRegister] using congrArg (fun word => word i) hl
    · intro i
      simpa only [Fin.append_right,rightRegister] using congrArg (fun word => word i) hr

/-- The actual platform input state is exactly the full computational-basis
word consisting of its input followed by the required zero ancillas. -/
theorem basisInput_eq_computationalBasis {n a : ℕ} (input : Bits n) :
    basisInput (a := a) input=computationalBasis (Fin.append input (fun _ => false)) := by
  funext state
  unfold basisInput computationalBasis
  congr 1
  apply propext
  rw [append_registers_iff]
  simp only [funext_iff,leftRegister,rightRegister]

theorem computationalBasis_tensor {n m : ℕ} (left : Bits n) (right : Bits m) :
    computationalBasis (Fin.append left right)=tensorState (computationalBasis left) (computationalBasis right) := by
  funext state
  change (if state=Fin.append left right then (1 : ℂ) else 0)=
    (if leftRegister state=left then 1 else 0)*(if rightRegister state=right then 1 else 0)
  by_cases hl : leftRegister state=left
  · by_cases hr : rightRegister state=right
    · rw [if_pos ((append_registers_iff state left right).mpr ⟨hl,hr⟩),if_pos hl,if_pos hr,mul_one]
    · have hs : state ≠ Fin.append left right := fun h => hr ((append_registers_iff state left right).mp h).2
      rw [if_neg hs,if_pos hl,if_neg hr,mul_zero]
  · have hs : state ≠ Fin.append left right := fun h => hl ((append_registers_iff state left right).mp h).1
    rw [if_neg hs,if_neg hl,zero_mul]

/-- Conditional basis outputs retain an orthogonal copy of every coin word. -/
theorem coinBasisBranch_sum {coins body : ℕ} (outputs : Bits coins → Bits body) :
    coinBranchState (fun coin => computationalBasis (outputs coin))=
      ∑ coin : Bits coins,coinAmplitude coins • computationalBasis (Fin.append coin (outputs coin)) := by
  classical
  simp_rw [computationalBasis_tensor]
  funext state
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,tensorState,computationalBasis,coinBranchState]
  rw [Finset.sum_eq_single (leftRegister state)]
  · simp
  · intro coin _ hne
    simp [Ne.symm hne]
  · simp

end InfoLossLAR.WorstCase

end P2MDyadicModule49

/- Helper module Solutions.RegevBridgeTM2Quantum. -/
section P2MDyadicModule50

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing QAlgorithms.Complexity

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

theorem wordExtension_before (word : List Bool) (i : ℕ) (h : i < word.length) :
    wordExtension word i = word[i] := by simp only [wordExtension, List.getElem?_eq_getElem h, Option.getD_some]

theorem wordExtension_after (word : List Bool) (i : ℕ) (h : word.length ≤ i) :
    wordExtension word i = false := by simp only [wordExtension, List.getElem?_eq_none h, Option.getD_none]

theorem wordExtension_basis (word : List Bool) (ancillas : ℕ) :
    Fin.append (toBits word) (fun _ : Fin (ancillas + 1) => false) =
      (fun i : Fin (word.length + (ancillas + 1)) => wordExtension word i.val) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [Fin.append_left, Fin.coe_castAdd, toBits, List.get_eq_getElem] using
      (wordExtension_before word j.val j.isLt).symm
  · intro j
    simp only [Fin.append_right, Fin.val_natAdd]
    exact (wordExtension_after word _ (Nat.le_add_right _ _)).symm

/-- Reading any output slot of the compiled basis state recovers the actual budgeted machine field. -/
theorem machineCircuit_output (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks : ℕ) (word : List Bool)
    (hsize : word.length + programPushBound program * ticks ≤ width) (i : Slot K Λ σ width) :
    (fun j => BooleanProgram.run word.length
      (machineProgram hw program input main initialState ticks word.length).ops (wordExtension word) j.val)
      (machineOutputWire hw program input main initialState ticks word.length i) =
      configurationBit ((stickyStep program)^[ticks] (initialConfiguration input main initialState word)) i :=
  machineProgram_semantics hw program input main initialState ticks word (wordExtension word)
    (wordExtension_before word) hsize i

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule50

/- Helper module Solutions.RegevBridgeTM2CodeDescription. -/
section P2MDyadicModule51

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

@[fun_prop] theorem description_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) :
    Poly (fun x : Request × ℕ => description program input main initialState x.1 x.2) := by
  unfold description
  fun_prop

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule51

/- Helper module Solutions.RegevBridgeTM2PolyCircuit. -/
section P2MDyadicModule52

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing StateTransition QAlgorithms.Complexity

open Integration9_9.TM2OutputLength

open OAI.MetricKMedian.Binary

namespace PolyProgramCircuit

variable {f : Str → Str} (P : PolyProgram id id f)

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqLabelMachineListBool_solutions

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqStateMachineListBool_solutions

theorem final_configuration (word : Str) :
    (stickyStep P.machine.code)^[P.time.eval word.length]
      (initialConfiguration P.machine.input P.machine.main P.machine.initial word) =
        P.machine.finalCfg (f word) := by
  have hh := P.outputs word
  change EvalsToInTime (TM2.step P.machine.code)
    (initialConfiguration P.machine.input P.machine.main P.machine.initial word)
    (some (P.machine.finalCfg (f word))) (P.time.eval word.length) at hh
  exact sticky_iterate_of_outputs P.machine.code _ _ _ hh rfl

/-- An actual output wire gives each present/absent symbol of the encoded function output. -/
theorem output_correct (word : Str) (i : Fin (capacity P word.length)) (b : Option Bool) :
    result P word (outputWire P word.length i b) = decide (b = (f word)[i.val]?) := by
  have hh := machineCircuit_output (capacity_pos P word.length) P.machine.code P.machine.input P.machine.main
    P.machine.initial (P.time.eval word.length) word (by unfold capacity; omega)
    (.inr (.inr (P.machine.output, i, b)))
  rw [final_configuration P word] at hh
  simpa only [result, outputWire, compiled, configurationBit, Machine.finalCfg, ↓reduceIte] using hh

theorem spacePolynomial_eval (length : ℕ) :
    (spacePolynomial P).eval length =
      (1 + P.time.eval length * transitionBound P.machine.code 0) *
        Fintype.card (Slot P.machine.K P.machine.Label P.machine.State (capacity P length)) := by
  simp only [spacePolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, slot_count, capacity]
  ring

theorem ancilla_bound (length : ℕ) : (compiled P length).ops.length ≤ (spacePolynomial P).eval length := by
  rw [spacePolynomial_eval]
  exact machineProgram_length_le _ _ _ _ _ _ _

end PolyProgramCircuit

end InfoLossLAR.WorstCase.TM2Boolean

end

end P2MDyadicModule52

/- Helper module Solutions.RegevBridgeTM2PolyUniform. -/
section P2MDyadicModule53

set_option autoImplicit false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open Turing StateTransition QAlgorithms.Complexity Polynomial

open Integration9_9.TM2OutputLength Integration9_9.TM2PlatformSerialization

open Integration9_9.TM2PolynomialBudget

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open CodeGenerator

variable {f : Str → Str} (P : PolyProgram id id f)

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqLabelMachineListBool_solutions_1

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqStateMachineListBool_solutions_1

@[fun_prop] theorem request_poly : Poly (request P) := by
  unfold request
  fun_prop

@[fun_prop] theorem descriptionGenerator_poly : Poly (descriptionGenerator P) := by
  unfold descriptionGenerator outputIndex
  fun_prop

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

end

end P2MDyadicModule53

/- Helper module Solutions.AdvantageBridgeQueryQuantum. -/
section P2MDyadicModule54

set_option autoImplicit false

set_option maxHeartbeats 500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open Integration9_9.TM2OutputLength

/-- The real machine's complete output fits in the compiled finite slot register. -/
theorem actualOutput_length_lt_capacity {f : Str → Str} (P : PolyProgram id id f) (word : Str) :
    (f word).length<capacity P word.length := by
  have h := output_length_le P.machine.tm word (f word) (P.time.eval word.length) (P.outputs word)
  change (f word).length≤word.length+programPushBound P.machine.code*P.time.eval word.length at h
  unfold capacity
  omega

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary

open LARRankOneMachine

end Integration9_9.LARCoinLayout

end P2MDyadicModule54

/- Helper module Solutions.AdvantageBridgeQueryMetadata. -/
section P2MDyadicModule55

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open CodeGenerator

variable {f : Str → Str} (P : PolyProgram id id f)

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqLabelMachineListBool_solutions_3

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqStateMachineListBool_solutions_3

@[fun_prop] theorem outputSlotIndex_poly :
    Poly (fun x : ℕ × ℕ => outputSlotIndex P x.1 x.2) := by
  unfold outputSlotIndex
  fun_prop

theorem outputSlotIndex_eq (width : ℕ) (index : Fin width) :
    outputSlotIndex P width index.val=
      (slotEquiv P.machine.K P.machine.Label P.machine.State width
        (.inr (.inr (P.machine.output,index,some true)))).val :=
  (slot_stack_index width P.machine.output index (some true)).symm

@[fun_prop] theorem generatedOutputAddress_poly :
    Poly (fun x : Request × ℕ => generatedOutputAddress P x.1 x.2) := by
  unfold generatedOutputAddress
  fun_prop

theorem generatedOutputAddress_eq (x : Request) (hw : 0<x.2.1.length) (index : Fin x.2.1.length) :
    generatedOutputAddress P x index.val=
      (machineProgram hw P.machine.code P.machine.input P.machine.main P.machine.initial
        x.2.2.length x.1.length).output (.inr (.inr (P.machine.output,index,some true))) := by
  unfold generatedOutputAddress
  rw [outputSlotIndex_eq]
  exact (generate_machineProgram P.machine.code P.machine.input P.machine.main P.machine.initial x hw).2.2 _

@[fun_prop] theorem generatedProgramOutputAddress_poly :
    Poly (fun x : Str × ℕ => generatedProgramOutputAddress P x.1 x.2) := by
  unfold generatedProgramOutputAddress
  fun_prop

/-- Exact transport of the physical program output across an equal stack capacity. -/
theorem outputProgram_transport {a b : ℕ} (he : a=b) (ha : 0<a) (hb : 0<b)
    (ticks length : ℕ) (index : Fin a) :
    (machineProgram ha P.machine.code P.machine.input P.machine.main P.machine.initial ticks length).output
      (.inr (.inr (P.machine.output,index,some true)))=
    (machineProgram hb P.machine.code P.machine.input P.machine.main P.machine.initial ticks length).output
      (.inr (.inr (P.machine.output,Fin.cast he index,some true))) := by
  cases he
  rfl

/-- On each unary request, the emitted natural address is literally the
physical outputWire of the verified uniform compiler. -/
theorem generatedProgramOutputAddress_eq (length : ℕ) (index : Fin (capacity P length)) :
    generatedProgramOutputAddress P (unary length) index.val=(outputWire P length index (some true)).val := by
  unfold generatedProgramOutputAddress
  rw [request_unary]
  let width := (List.replicate (capacity P length) ()).length
  have hwidth : width=capacity P length := List.length_replicate
  have hw : 0<width := by rw [hwidth]; exact capacity_pos P length
  let i : Fin width := ⟨index.val,by rw [hwidth]; exact index.isLt⟩
  have hi : Fin.cast hwidth i=index := Fin.ext rfl
  have h := generatedOutputAddress_eq P
    (List.replicate length (),List.replicate (capacity P length) (),List.replicate (P.time.eval length) ()) hw i
  simp only [List.length_replicate] at h
  have he := outputProgram_transport P hwidth hw (capacity_pos P length) (P.time.eval length) length i
  rw [he,hi] at h
  simpa only [outputWire,machineOutputWire,compiled,i] using h

@[fun_prop] theorem generatedAddressRange_poly :
    Poly (fun x : Str × (List Unit × ℕ) => generatedAddressRange P x.1 x.2.1 x.2.2) := by
  unfold generatedAddressRange
  apply Automatic.Poly.list_map
  · fun_prop
  · exact Automatic.Poly.comp (f := fun xs : List Unit => List.range xs.length)
      (g := fun x : Str × (List Unit × ℕ) => x.2.1) Automatic.Poly.list_indices (by fun_prop)

/-- All genuinely emitted addresses lie inside the actual physical circuit
register whenever the requested output cells fit its proved capacity. -/
theorem generatedAddressRange_bounded (length : ℕ) (slots : List Unit) (offset : ℕ)
    (h : offset+slots.length ≤ capacity P length) :
    ∀ address∈generatedAddressRange P (unary length) slots offset,
      address<length+((compiled P length).ops.length+1) := by
  intro address ha
  obtain ⟨index,hi,rfl⟩ := List.mem_map.mp ha
  have hin := List.mem_range.mp hi
  let cell : Fin (capacity P length) := ⟨offset+index,by omega⟩
  change generatedProgramOutputAddress P (unary length) cell.val<_
  rw [generatedProgramOutputAddress_eq]
  exact (outputWire P length cell (some true)).isLt

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

end

end P2MDyadicModule55

/- Helper module Solutions.AdvantageBridgeMultiSelector. -/
section P2MDyadicModule56

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

theorem multiSelectorChunk_valid (start left : ℕ) (choice : ℕ × ℕ)
    (hl : left<start) (hf : choice.1<start) (hr : choice.2<start) :
    BooleanProgram.Valid start (multiSelectorChunk start left choice) := by
  simp_all [multiSelectorChunk,BooleanProgram.Valid,BooleanOp.Valid,BooleanOp.sources]
  omega

theorem multiSelectorOps_valid (start left : ℕ) (choices : List (ℕ × ℕ))
    (hl : left<start) (hc : ∀ choice∈choices,choice.1<start ∧ choice.2<start) :
    BooleanProgram.Valid start (multiSelectorOps start left choices) := by
  induction choices generalizing start left with
  | nil => trivial
  | cons choice rest ih =>
    rw [multiSelectorOps,BooleanProgram.valid_append]
    have hf := hc choice (by simp)
    refine ⟨multiSelectorChunk_valid start left choice hl hf.1 hf.2,?_⟩
    change BooleanProgram.Valid (start+4) (multiSelectorOps (start+4) (start+3) rest)
    apply ih (start+4) (start+3) (by omega)
    intro other ho
    have h := hc other (by simp [ho])
    omega

theorem multiSelectorChunk_value (start left : ℕ) (choice : ℕ × ℕ) (state : ℕ → Bool)
    (hl : left<start) (hf : choice.1<start) (hr : choice.2<start) :
    BooleanProgram.run start (multiSelectorChunk start left choice) state (start+3)=
      if state choice.1 then state choice.2 else state left := by
  cases hflag : state choice.1 <;> cases hleft : state left <;> cases hright : state choice.2 <;>
    simp (disch := omega) [multiSelectorChunk,BooleanProgram.run,BooleanOp.assign,BooleanOp.eval,
      Function.update_apply,hflag,hleft,hright]

theorem multiSelectorValue_congr (choices : List (ℕ × ℕ)) (first second : ℕ → Bool)
    (initial : Bool) (h : ∀ choice∈choices,first choice.1=second choice.1 ∧ first choice.2=second choice.2) :
    multiSelectorValue first initial choices=multiSelectorValue second initial choices := by
  induction choices generalizing initial with
  | nil => rfl
  | cons choice rest ih =>
    have hc := h choice (by simp)
    simp only [multiSelectorValue,hc.1,hc.2]
    exact ih _ (fun other ho => h other (by simp [ho]))

/-- Exact multi-output selection for arbitrary basis values. Flags and candidate
outputs remain original read-only wires; all writes use four fresh wires per choice. -/
theorem multiSelectorOps_value (start left : ℕ) (choices : List (ℕ × ℕ)) (state : ℕ → Bool)
    (hl : left<start) (hc : ∀ choice∈choices,choice.1<start ∧ choice.2<start) :
    BooleanProgram.run start (multiSelectorOps start left choices) state
      (multiSelectorOutput start left choices)=multiSelectorValue state (state left) choices := by
  induction choices generalizing start left state with
  | nil => rfl
  | cons choice rest ih =>
    have hf := hc choice (by simp)
    rw [multiSelectorOps,BooleanProgram.run_append]
    change BooleanProgram.run (start+4) (multiSelectorOps (start+4) (start+3) rest)
      (BooleanProgram.run start (multiSelectorChunk start left choice) state)
      (multiSelectorOutput (start+4) (start+3) rest)=_
    rw [ih (start+4) (start+3) _ (by omega) (fun other ho => by
      have h := hc other (by simp [ho]); omega)]
    rw [multiSelectorChunk_value start left choice state hl hf.1 hf.2]
    rw [multiSelectorValue_congr rest _ state _ (fun other ho => by
      have h := hc other (by simp [ho])
      exact ⟨BooleanProgram.run_below start _ state _ h.1,BooleanProgram.run_below start _ state _ h.2⟩)]
    rfl

/-- The complete, literal Clifford+T chain selects the stated event on arbitrary
input amplitudes supported on zero-initialized fresh scratch wires. -/
theorem multiSelector_probability {n start left : ℕ} (choices : List (ℕ × ℕ))
    (hl : left<start) (hc : ∀ choice∈choices,choice.1<start ∧ choice.2<start)
    (hn : start+4*choices.length ≤ n) (state : QState n)
    (hz : ∀ input,state input≠0 → ∀ index,start ≤ index → index<start+4*choices.length →
      selectorBitsExtension input index=false) :
    (∑ output : Bits n,if output ⟨multiSelectorOutput start left choices,
        (multiSelectorOutput_lt start left choices hl).trans_le hn⟩ then
      ‖runLayered (compileReversible (booleanToReversible
        (BooleanProgram.gates start (multiSelectorOps start left choices)
          (by rw [multiSelectorOps_length]; exact hn)))) state output‖^2 else 0)=
      ∑ input : Bits n,if multiSelectorValue (selectorBitsExtension input)
        (selectorBitsExtension input left) choices then ‖state input‖^2 else 0 := by
  have hbound : start+(multiSelectorOps start left choices).length≤n := by
    rw [multiSelectorOps_length]; exact hn
  have hzero (input : Bits n) (hi : state input≠0)
      (gate : BooleanGate n) (hg : gate∈BooleanProgram.gates start (multiSelectorOps start left choices) hbound) :
      input gate.target=false := by
    have ht := BooleanProgram.target_range (multiSelectorOps start left choices) hbound gate hg
    rw [multiSelectorOps_length] at ht
    simpa only [selectorBitsExtension_get] using hz input hi gate.target.val ht.1 ht.2
  rw [booleanCircuit_event_probability _ (BooleanProgram.fresh _ hbound) state hzero]
  apply Finset.sum_congr rfl
  intro input hi
  have he : (fun i : Fin n => selectorBitsExtension input i.val)=input := by
    funext i; simp
  have hsem := BooleanProgram.semantics (multiSelectorOps start left choices) hbound
    (multiSelectorOps_valid start left choices hl hc) (selectorBitsExtension input)
  rw [he] at hsem
  have hv := congrFun hsem (⟨multiSelectorOutput start left choices,
    (multiSelectorOutput_lt start left choices hl).trans_le hn⟩ : Fin n)
  simp only [Fin.val_mk,multiSelectorOps_value start left choices _ hl hc] at hv
  rw [hv]

/-- If the accumulator and every enabled candidate have the same Boolean value,
all later concrete selector stages preserve that value. -/
theorem multiSelectorValue_invariant (state : ℕ → Bool) (value : Bool) (choices : List (ℕ × ℕ))
    (h : ∀ choice∈choices,state choice.1=true → state choice.2=value) :
    multiSelectorValue state value choices=value := by
  induction choices with
  | nil => rfl
  | cons choice rest ih =>
    have hr := ih (fun other ho => h other (by simp [ho]))
    cases hf : state choice.1
    · simpa only [multiSelectorValue,hf,Bool.false_eq_true,ite_false] using hr
    · simpa only [multiSelectorValue,hf,ite_true,h choice (by simp) hf] using hr

/-- A selected candidate is obtained exactly when an enabled candidate exists
and all enabled outputs equal it; no probabilistic experiment equality is assumed. -/
theorem multiSelectorValue_selected (state : ℕ → Bool) (value initial : Bool) (choices : List (ℕ × ℕ))
    (h : ∀ choice∈choices,state choice.1=true → state choice.2=value)
    (hex : ∃ choice∈choices,state choice.1=true) :
    multiSelectorValue state initial choices=value := by
  induction choices generalizing initial with
  | nil => simpa using hex
  | cons choice rest ih =>
    have hr : ∀ other∈rest,state other.1=true → state other.2=value :=
      fun other ho => h other (by simp [ho])
    cases hf : state choice.1
    · have ht : ∃ other∈rest,state other.1=true := by
        obtain ⟨other,ho,ha⟩ := hex
        rcases List.mem_cons.mp ho with he|ho
        · subst other; simp [hf] at ha
        · exact ⟨other,ho,ha⟩
      simpa only [multiSelectorValue,hf,Bool.false_eq_true,ite_false] using ih initial hr ht
    · simp only [multiSelectorValue,hf,ite_true,h choice (by simp) hf]
      exact multiSelectorValue_invariant state value rest hr

end InfoLossLAR.WorstCase

end P2MDyadicModule56

/- Helper module Solutions.AdvantageBridgeMultiSelectorEmitter. -/
section P2MDyadicModule57

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime Integration9_9.TM2PlatformSerialization

open TM2Boolean.RPN

@[fun_prop] theorem multiSelectorNodeChunk_poly :
    Poly (fun x : ℕ × (ℕ × (ℕ × ℕ)) => multiSelectorNodeChunk x.1 x.2.1 x.2.2) := by
  unfold multiSelectorNodeChunk
  fun_prop

theorem multiSelectorNodeChunk_eq (start left : ℕ) (choice : ℕ × ℕ) :
    multiSelectorNodeChunk start left choice=(multiSelectorChunk start left choice).map node := rfl

@[fun_prop] theorem multiSelectorNodes_poly :
    Poly (fun x : ℕ × (ℕ × List (ℕ × ℕ)) => multiSelectorNodes x.1 x.2.1 x.2.2) := by
  unfold multiSelectorNodes
  apply Poly.list_flatMap
  · fun_prop
  · exact Poly.comp (f := fun xs : List (ℕ × ℕ) => List.range xs.length)
      (g := fun x : ℕ × (ℕ × List (ℕ × ℕ)) => x.2.2) Poly.list_indices (by fun_prop)

theorem multiSelectorNodes_eq (start left : ℕ) (choices : List (ℕ × ℕ)) :
    multiSelectorNodes start left choices=(multiSelectorOps start left choices).map node := by
  induction choices generalizing start left with
  | nil => rfl
  | cons choice rest ih =>
    simp only [multiSelectorNodes,List.length_cons,List.range_succ_eq_map,List.flatMap_cons,
      List.flatMap_map,Function.comp_def,Nat.mul_zero,Nat.add_zero,ite_true,
      List.getElem?_cons_zero,Option.getD_some,multiSelectorOps,List.map_append]
    rw [←multiSelectorNodeChunk_eq,←ih]
    congr 1
    apply List.flatMap_congr
    intro index hi
    have hs : start+4*(index+1)=(start+4)+4*index := by omega
    have hl : (if index+1=0 then left else start+4*(index+1)-1)=
        (if index=0 then start+3 else (start+4)+4*index-1) := by
      by_cases hi : index=0
      · subst index; simp
      · simp only [if_neg (by omega : index+1≠0),if_neg hi,hs]
    simp only [Nat.succ_eq_add_one,List.getElem?_cons_succ]
    rw [hl,hs]

@[fun_prop] theorem multiSelectorGateWords_poly :
    Poly (fun x : List Unit × (ℕ × (ℕ × List (ℕ × ℕ))) =>
      multiSelectorGateWords x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold multiSelectorGateWords
  fun_prop

theorem multiSelectorGateWords_correct {total : ℕ} (slots : List Unit)
    (start left : ℕ) (choices : List (ℕ × ℕ))
    (hl : left<start) (hc : ∀ choice∈choices,choice.1<start ∧ choice.2<start)
    (hn : start+4*choices.length ≤ total) (hs : start+4*choices.length ≤ slots.length) :
    multiSelectorGateWords slots start left choices=
      (BooleanProgram.gates start (multiSelectorOps start left choices)
        (by simpa only [multiSelectorOps_length] using hn)).map BooleanGate.code := by
  unfold multiSelectorGateWords
  rw [multiSelectorNodes_eq]
  exact instructionWords_gates slots start (multiSelectorOps start left choices)
    (by simpa only [multiSelectorOps_length] using hn) (multiSelectorOps_valid start left choices hl hc)
    (by simpa only [multiSelectorOps_length] using hs)

@[fun_prop] theorem multiSelectorFinalIndex_poly :
    Poly (fun x : ℕ × (ℕ × List (ℕ × ℕ)) => multiSelectorFinalIndex x.1 x.2.1 x.2.2) := by
  unfold multiSelectorFinalIndex
  fun_prop

theorem multiSelectorFinalIndex_eq (start left : ℕ) (choices : List (ℕ × ℕ)) :
    multiSelectorFinalIndex start left choices=multiSelectorOutput start left choices := by
  induction choices generalizing start left with
  | nil => rfl
  | cons choice rest ih =>
    simp only [multiSelectorOutput,←ih,multiSelectorFinalIndex,List.isEmpty_cons,Bool.false_eq_true,ite_false]
    cases rest with
    | nil => simp
    | cons next remaining =>
      simp only [List.isEmpty_cons,Bool.false_eq_true,ite_false,List.length_cons]
      omega

@[fun_prop] theorem multiSelectorScratch_poly : Poly multiSelectorScratch := by
  unfold multiSelectorScratch
  fun_prop

end InfoLossLAR.WorstCase

end P2MDyadicModule57

/- Helper module Solutions.AdvantageBridgeRegisterLoad. -/
section P2MDyadicModule58

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean.RPN

theorem registerLoadOp_valid (start : ℕ) (source : Bool × ℕ)
    (h : source.1=true → source.2<start) : (registerLoadOp source).Valid start := by
  cases hs : source.1
  · simp [registerLoadOp,hs,BooleanOp.Valid,BooleanOp.sources]
  · simpa [registerLoadOp,hs,BooleanOp.Valid,BooleanOp.sources] using h hs

theorem registerLoadOps_valid (start : ℕ) (sources : List (Bool × ℕ))
    (h : ∀ source∈sources,source.1=true → source.2<start) :
    BooleanProgram.Valid start (registerLoadOps sources) := by
  induction sources generalizing start with
  | nil => trivial
  | cons source rest ih =>
    change (registerLoadOp source).Valid start ∧ BooleanProgram.Valid (start+1) (registerLoadOps rest)
    refine ⟨registerLoadOp_valid start source (h source (by simp)),?_⟩
    apply ih (start+1)
    intro other ho ht
    exact (h other (by simp [ho]) ht).trans (by omega)

theorem registerLoadOp_value (source : Bool × ℕ) (state : ℕ → Bool) :
    (registerLoadOp source).eval state=registerLoadValue source state := by
  cases hs : source.1 <;> simp [registerLoadOp,registerLoadValue,BooleanOp.eval,hs]

/-- Every actually written wire has its stated old-input value; later copies
read only the original register, even when source addresses are repeated. -/
theorem registerLoadOps_value (start : ℕ) (sources : List (Bool × ℕ))
    (h : ∀ source∈sources,source.1=true → source.2<start) (state : ℕ → Bool)
    (index : ℕ) (hi : index<sources.length) :
    BooleanProgram.run start (registerLoadOps sources) state (start+index)=
      registerLoadValue sources[index] state := by
  induction sources generalizing start index state with
  | nil => simp at hi
  | cons source rest ih =>
    cases index with
    | zero =>
      change BooleanProgram.run (start+1) (registerLoadOps rest)
        ((registerLoadOp source).assign start state) (start+0)=_
      rw [BooleanProgram.run_below _ _ _ _ (by omega)]
      simp only [Nat.add_zero,BooleanOp.assign,Function.update_self,List.getElem_cons_zero,registerLoadOp_value]
    | succ index =>
      have hindex : index<rest.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi
      change BooleanProgram.run (start+1) (registerLoadOps rest)
        ((registerLoadOp source).assign start state) (start+(index+1))=_
      rw [show start+(index+1)=(start+1)+index by omega,
        ih (start+1) (fun other ho ht => (h other (by simp [ho]) ht).trans (by omega)) _ index hindex]
      simp only [List.getElem_cons_succ,registerLoadValue]
      cases ht : rest[index].1
      · simp [ht]
      · have hb := h rest[index] (by simp) ht
        simp only [ht,ite_true,BooleanOp.assign]
        exact Function.update_of_ne (by omega) _ _

@[fun_prop] theorem registerLoadNode_poly : Poly registerLoadNode := by
  unfold registerLoadNode
  fun_prop

theorem registerLoadNode_eq (source : Bool × ℕ) : registerLoadNode source=node (registerLoadOp source) := by
  cases hs : source.1 <;> simp [registerLoadNode,registerLoadOp,node,hs]

@[fun_prop] theorem registerLoadGateWords_poly :
    Poly (fun x : List Unit × (ℕ × List (Bool × ℕ)) => registerLoadGateWords x.1 x.2.1 x.2.2) := by
  unfold registerLoadGateWords
  fun_prop

theorem registerLoadGateWords_correct {total : ℕ} (slots : List Unit) (start : ℕ)
    (sources : List (Bool × ℕ)) (h : ∀ source∈sources,source.1=true → source.2<start)
    (hn : start+sources.length ≤ total) (hs : start+sources.length ≤ slots.length) :
    registerLoadGateWords slots start sources=
      (BooleanProgram.gates start (registerLoadOps sources)
        (by simpa only [registerLoadOps_length] using hn)).map BooleanGate.code := by
  unfold registerLoadGateWords
  have he : sources.map registerLoadNode=(registerLoadOps sources).map node := by
    change sources.map registerLoadNode=(sources.map registerLoadOp).map node
    rw [List.map_map]
    exact List.map_congr_left (fun source _ => registerLoadNode_eq source)
  rw [he]
  exact instructionWords_gates slots start (registerLoadOps sources)
    (by simpa only [registerLoadOps_length] using hn) (registerLoadOps_valid start sources h)
    (by simpa only [registerLoadOps_length] using hs)

end InfoLossLAR.WorstCase

end P2MDyadicModule58

/- Helper module Solutions.AdvantageBridgeBundleEmitter. -/
section P2MDyadicModule59

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem unaryPayload_poly : Poly unaryPayload := by
  unfold unaryPayload
  exact Poly.comp parser_take_poly (Poly.pair Poly.identity inputWidth_poly)

@[fun_prop] theorem shiftWireWord_poly : Poly (fun input : Str × Str => shiftWireWord input.1 input.2) := by
  unfold shiftWireWord
  fun_prop

@[fun_prop] theorem shiftInstructionWord_poly : Poly (fun input : Str × Str => shiftInstructionWord input.1 input.2) := by
  unfold shiftInstructionWord
  fun_prop

/-- The emitter offsets exactly the actual right-embedded platform gate. -/
theorem shiftInstructionWord_encInstr {n : ℕ} (prior : Str) (gate : Instr n) :
    shiftInstructionWord prior (encInstr gate)=encInstr (rightInstruction (n := prior.length) gate) := by
  cases gate <;>
    simp only [encInstr,List.append_assoc,shiftInstructionWord,readUnary_append,emitter_width_append,
      unaryPayload_encNat,unaryPayload_number,lengthToken_eq,List.length_append,unary,List.length_replicate,
      rightInstruction,Fin.val_natAdd] <;> norm_num <;> rfl

@[fun_prop] theorem shiftCircuitWords_poly :
    Poly (fun input : Str × List (List Str) => shiftCircuitWords input.1 input.2) := by
  have hg : Poly (fun x : ((Str × List (List Str)) × List Str) × Str =>
      shiftInstructionWord x.1.1.1 x.2) :=
    Poly.comp (f := fun p : Str × Str => shiftInstructionWord p.1 p.2)
      (g := fun x : ((Str × List (List Str)) × List Str) × Str => (x.1.1.1,x.2))
      shiftInstructionWord_poly (by fun_prop)
  have hl : Poly (fun x : (Str × List (List Str)) × List Str =>
      x.2.map (shiftInstructionWord x.1.1)) := Poly.list_map hg Poly.snd
  unfold shiftCircuitWords
  exact Poly.list_map hl Poly.snd

theorem shiftCircuitWords_correct {n : ℕ} (prior : Str) (circuit : Layered n) :
    shiftCircuitWords prior (circuit.map (List.map encInstr))=
      (rightCircuit (n := prior.length) circuit).map (List.map encInstr) := by
  simp only [shiftCircuitWords,rightCircuit,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro gate _
  exact shiftInstructionWord_encInstr prior gate

@[fun_prop] theorem readFamilyFrame_poly : Poly readFamilyFrame := by
  unfold readFamilyFrame
  fun_prop

@[fun_prop] theorem precedingWireSlots_poly : Poly precedingWireSlots := by
  unfold precedingWireSlots
  apply Poly.list_flatMap
  · fun_prop
  · exact Poly.comp parser_take_poly Poly.identity

@[fun_prop] theorem bundleCircuitWordLayers_poly : Poly bundleCircuitWordLayers := by
  unfold bundleCircuitWordLayers
  apply Poly.list_flatMap
  · exact Poly.comp shiftCircuitWords_poly
      (Poly.pair precedingWireSlots_poly (by fun_prop))
  · exact Poly.list_indices

@[fun_prop] theorem bundleOutputWords_poly : Poly bundleOutputWords := by
  unfold bundleOutputWords
  apply Poly.list_map
  · exact Poly.comp shiftWireWord_poly (Poly.pair precedingWireSlots_poly (by fun_prop))
  · exact Poly.list_indices

private theorem emitter_read_number (number : ℕ) : readUnary (encNat number)=(encNat number,[]) := by
  simpa only [List.append_nil] using readUnary_append number []

theorem shiftInstructionWord_spec (prior xs : Str) :
    shiftInstructionWord prior xs=
      encNat (inputWidth xs)++encNat (prior.length+inputWidth (readUnary xs).2)++
        (if inputWidth xs=4 then
          encNat (prior.length+inputWidth (readUnary (readUnary xs).2).2) else []) := by
  unfold shiftInstructionWord
  simp only [lengthToken_eq,List.length_append,unaryPayload_length]
  split_ifs <;> simp

theorem shiftInstructionWord_canonical (prior : Str) (tag first second : ℕ) :
    shiftInstructionWord prior (encNat tag++encNat first++(if tag=4 then encNat second else []))=
      encNat tag++encNat (prior.length+first)++(if tag=4 then encNat (prior.length+second) else []) := by
  rw [shiftInstructionWord_spec]
  by_cases h : tag=4 <;>
    simp [h,List.append_assoc,readUnary_append,emitter_width_append,emitter_width_number,emitter_read_number]

/-- Offset composition is exact even on malformed original gate words,
because every shifted word is canonically unary-framed. -/
theorem shiftInstructionWord_comp (first second xs : Str) :
    shiftInstructionWord first (shiftInstructionWord second xs)=shiftInstructionWord (first++second) xs := by
  rw [shiftInstructionWord_spec second xs,shiftInstructionWord_canonical,shiftInstructionWord_spec]
  simp only [List.length_append,Nat.add_assoc]

theorem shiftCircuitWords_comp (first second : Str) (layers : List (List Str)) :
    shiftCircuitWords first (shiftCircuitWords second layers)=shiftCircuitWords (first++second) layers := by
  simp only [shiftCircuitWords,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro word _
  exact shiftInstructionWord_comp first second word

theorem shiftCircuitWords_flatMap {α : Type*} (prior : Str) (values : List α) (layers : α → List (List Str)) :
    shiftCircuitWords prior (values.flatMap layers)=values.flatMap (fun value => shiftCircuitWords prior (layers value)) := by
  simp only [shiftCircuitWords,List.map_flatMap]

theorem shiftCircuitWords_zero {n : ℕ} (circuit : Layered n) :
    shiftCircuitWords [] (circuit.map (List.map encInstr))=circuit.map (List.map encInstr) := by
  simp only [shiftCircuitWords,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro gate _
  rw [shiftInstructionWord_encInstr]
  cases gate <;> simp [rightInstruction,encInstr]

/-- The polynomial indexed emitter has exactly the recursive physical
head/offset-tail composition, with a canonicalized head layer description. -/
theorem bundleCircuitWordLayers_cons (frame : PhysicalFrameWords) (frames : List PhysicalFrameWords) :
    bundleCircuitWordLayers (frame::frames)=
      shiftCircuitWords [] frame.2.2++shiftCircuitWords frame.1 (bundleCircuitWordLayers frames) := by
  unfold bundleCircuitWordLayers
  simp only [List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,
    List.getElem?_cons_zero,Option.getD_some,precedingWireSlots,List.take_zero,List.flatMap_nil]
  rw [shiftCircuitWords_flatMap]
  apply congrArg (fun tail => shiftCircuitWords [] frame.2.2++tail)
  apply List.flatMap_congr
  intro index _
  simp only [List.getElem?_cons_succ,precedingWireSlots,List.take_succ_cons,List.flatMap_cons]
  exact (shiftCircuitWords_comp frame.1 _ _).symm

private theorem rightCircuit_words_cast {n : ℕ} (first second : ℕ) (h : first=second) (circuit : Layered n) :
    (rightCircuit (n := first) circuit).map (List.map encInstr)=
      (rightCircuit (n := second) circuit).map (List.map encInstr) := by
  cases h
  rfl

theorem bundleCircuitWordLayers_correct (blocks : List QuantumBlock) :
    bundleCircuitWordLayers (blocks.map blockFrameWords)=
      (bundleCircuit blocks).map (List.map encInstr) := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    rw [List.map_cons,bundleCircuitWordLayers_cons]
    simp only [blockFrameWords,shiftCircuitWords_zero]
    have hlen : (unary block.wires).length=block.wires := by simp [unary]
    have hshift : shiftCircuitWords (unary block.wires) ((bundleCircuit blocks).map (List.map encInstr))=
        (rightCircuit (n := block.wires) (bundleCircuit blocks)).map (List.map encInstr) := by
      exact (shiftCircuitWords_correct (unary block.wires) (bundleCircuit blocks)).trans
        (rightCircuit_words_cast _ _ hlen _)
    rw [ih,hshift]
    simp only [bundleCircuit,bundleWidth,List.map_append,leftCircuit,List.map_map,Function.comp_def,
      leftInstruction_encInstr]

@[fun_prop] theorem emitDOutputs_poly : Poly emitDOutputs := by
  unfold emitDOutputs
  exact Poly.comp bundleOutputWords_poly (Poly.list_map (Poly.comp readFamilyFrame_poly Poly.snd) Poly.identity)

end InfoLossLAR.WorstCase

end P2MDyadicModule59

/- Helper module Solutions.AdvantageBridgeBundleUniform. -/
section P2MDyadicModule60

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity Turing Function Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open Integration9_9 Integration9_9.TM2StockLists QMCNumericRuntime

theorem bundleRequests_correct (budget : Polynomial ℕ) (input : Str) :
    bundleRequests budget input = List.ofFn (fun index : Fin (budget.eval input.length+1) => unary index.val) := by
  apply List.ext_getElem
  · simp [bundleRequests,bundleRequestsFromSlots]
  · intro i hi hj
    simp only [bundleRequests,bundleRequestsFromSlots,List.length_map,List.length_range,
      List.length_replicate] at hi
    simp only [bundleRequests,bundleRequestsFromSlots,List.getElem_map,List.getElem_range,
      List.take_replicate,List.getElem_ofFn,List.map_replicate,unary]
    rw [Nat.min_eq_left (by omega)]

theorem generatedBundleDescriptions_correct (D : Family) (generator : Str → Str)
    (h : ∀ n,generator (unary n)=encFamilyAt D n) (budget : Polynomial ℕ) (input : Str) :
    generatedBundleDescriptions generator budget input=describedQueryBlocks D (budget.eval input.length) := by
  rw [generatedBundleDescriptions,bundleRequests_correct]
  simp only [List.map_ofFn,Function.comp_def,h,describedQueryBlocks]

end InfoLossLAR.WorstCase

end P2MDyadicModule60

/- Helper module Solutions.AdvantageBridgeDRegisterLoad. -/
section P2MDyadicModule61

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime

@[fun_prop] theorem dBlockLoadSources_poly :
    Poly (fun x : List ℕ × (List Unit × List Unit) => dBlockLoadSources x.1 x.2.1 x.2.2) := by
  unfold dBlockLoadSources
  apply Poly.list_map
  · fun_prop
  · exact Poly.comp (f := fun xs : List Unit => List.range xs.length)
      (g := fun x : List ℕ × (List Unit × List Unit) => x.2.2) Poly.list_indices (by fun_prop)

theorem dBlockLoadSources_valid (start : ℕ) (querySources : List ℕ) (request slots : List Unit)
    (hq : request.length ≤ querySources.length)
    (hs : ∀ address∈querySources,address  <  start) :
    ∀ source∈dBlockLoadSources querySources request slots,source.1=true → source.2  <  start := by
  intro source hsource ht
  obtain ⟨index,hi,he⟩ := List.mem_map.mp hsource
  rw [←he] at ht ⊢
  have hj : index  <  request.length := by simpa using ht
  have hindex : index  <  querySources.length := hj.trans_le hq
  simpa only [List.getElem?_eq_getElem hindex,Option.getD_some] using
    hs querySources[index] (List.getElem_mem hindex)

@[fun_prop] theorem dBundleLoadSources_poly :
    Poly (fun x : List ℕ × List (Str × Str) => dBundleLoadSources x.1 x.2) := by
  unfold dBundleLoadSources
  fun_prop

theorem dBundleLoadSources_valid (start : ℕ) (querySources : List ℕ) (descriptions : List (Str × Str))
    (hq : ∀ description∈descriptions,description.1.length ≤ querySources.length)
    (hs : ∀ address∈querySources,address  <  start) :
    ∀ source∈dBundleLoadSources querySources descriptions,source.1=true → source.2  <  start := by
  intro source hsource ht
  obtain ⟨description,hd,hmem⟩ := List.mem_flatMap.mp hsource
  exact dBlockLoadSources_valid start querySources _ _
    (by simpa only [List.length_map] using hq description hd) hs source hmem ht

/-- The true requests in the D bundle never ask for more than its padded width. -/
theorem describedQueryBlocks_request_bound (D : Family) (maximum : ℕ) :
    ∀ description∈describedQueryBlocks D maximum,description.1.length ≤ maximum := by
  intro description hd
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hd
  simp only [unary,List.length_replicate]
  omega

/-- On the exact actual D descriptions, the complete loader has genuine valid
sources as soon as the emitted query addresses fit the prefix register. -/
theorem dBundleLoadSources_actual_valid (start : ℕ) (D : Family) (maximum : ℕ) (querySources : List ℕ)
    (hl : querySources.length=maximum) (hs : ∀ address∈querySources,address < start) :
    ∀ source∈dBundleLoadSources querySources (describedQueryBlocks D maximum),
      source.1=true → source.2 < start :=
  dBundleLoadSources_valid start querySources _
    (fun description hd => (describedQueryBlocks_request_bound D maximum description hd).trans hl.ge) hs

end InfoLossLAR.WorstCase

end P2MDyadicModule61

/- Helper module Solutions.AdvantageBridgeQueryWiring. -/
section P2MDyadicModule62

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem queryWireRequest_poly (coins : Polynomial ℕ) : Poly (queryWireRequest coins) := by
  have hs : Poly (fun word : Str => List.replicate ((coins+X).eval (word.map (fun _ => ())).length) ()) :=
    Poly.comp (f := fun slots : List Unit => List.replicate ((coins+X).eval slots.length) ())
      (g := fun word : Str => word.map (fun _ => ()))
      (TM2PolynomialBudget.polynomialSlots_poly (coins+X)) (by fun_prop)
  exact Poly.comp (f := fun slots : List Unit => slots.map (fun _ => true))
    (g := fun word : Str => List.replicate ((coins+X).eval (word.map (fun _ => ())).length) ())
    (by fun_prop) hs

theorem queryWireRequest_unary (coins : Polynomial ℕ) (n : ℕ) :
    queryWireRequest coins (unary n)=unary (coins.eval n+n) := by
  simp only [queryWireRequest,List.length_map,unary,List.length_replicate,eval_add,eval_X,List.map_replicate]

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule62

/- Helper module Solutions.AdvantageBridgeSelectorWiring. -/
section P2MDyadicModule63

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime

/-- The actual D bundle's serialized global output addresses are all physical. -/
theorem emittedDOutputAddresses_valid (D : Family) (maximum : ℕ) (query : Str) :
    ∀ address∈(emitDOutputs (describedQueryBlocks D maximum)).map inputWidth,
      address < bundleWidth (queryBlocks D maximum query) := by
  intro address ha
  obtain ⟨token,ht,rfl⟩ := List.mem_map.mp ha
  rw [emitDOutputs_correct D maximum query] at ht
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp ht
  have hn (number : ℕ) : inputWidth (encNat number)=number := by
    rw [←unaryPayload_length,unaryPayload_number]
    simp only [unary,List.length_replicate]
  rw [hn]
  exact (bundleOutput (queryBlocks D maximum query) index).isLt

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule63

/- Helper module Solutions.AdvantageBridgeQueryPointerSemantics. -/
section P2MDyadicModule64

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

/-- The value at a really emitted pointer is the corresponding real machine
output bit, not an abstract address interpretation premise. -/
theorem generatedQueryBits_output {f : Str → Str} (P : PolyProgram id id f) (word : Str)
    (index : Fin (capacity P word.length)) :
    generatedQueryBits P word (generatedProgramOutputAddress P (unary word.length) index.val)=
      decide (some true=(f word)[index.val]?) := by
  rw [generatedProgramOutputAddress_eq]
  exact (selectorBitsExtension_get (result P word) (outputWire P word.length index (some true))).trans
    (output_correct P word index (some true))

/-- Generic pointer-list indexing, for any actual native function. -/
theorem generatedAddressRange_get_any {f : Str → Str} (P : PolyProgram id id f)
    (word : Str) (slots : List Unit) (offset index : ℕ) (hi : index < slots.length) :
    (generatedAddressRange P word slots offset)[index]'(by simpa only [generatedAddressRange,List.length_map,List.length_range] using hi)=
      generatedProgramOutputAddress P word (offset+index) := by
  simp only [generatedAddressRange,List.getElem_map,List.getElem_range]

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary

open LARRankOneMachine

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule64

/- Helper module Solutions.AdvantageBridgeInputCopy. -/
section P2MDyadicModule65

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime

@[fun_prop] theorem inputCopySources_poly :
    Poly (fun x : List Unit × List Unit => inputCopySources x.1 x.2) := by
  have hi : Poly (fun x : List Unit × List Unit => List.range x.2.length) :=
    Poly.comp (f := fun xs : List Unit => List.range xs.length) (g := Prod.snd)
      Poly.list_indices Poly.snd
  have hc : Poly (fun x : List Unit × List Unit => (List.range x.2.length).map (fun i => (true,i))) := by
    apply Poly.list_map
    · exact (by fun_prop : Poly (fun x : (List Unit × List Unit) × ℕ => (true,x.2)))
    · exact hi
  have hz : Poly (fun x : List Unit × List Unit => x.1.map (fun _ => (false,(0 : ℕ)))) := by
    fun_prop
  exact Poly.comp (f := fun x : List (Bool × ℕ) × List (Bool × ℕ) => x.1++x.2)
    (g := fun x : List Unit × List Unit =>
      (x.1.map (fun _ => (false,(0 : ℕ))),(List.range x.2.length).map (fun i => (true,i))))
    Poly.list_append (Poly.pair hz hc)

theorem inputCopySources_valid (coinSlots inputSlots : List Unit) :
    ∀ source∈inputCopySources coinSlots inputSlots,source.1=true → source.2 < inputSlots.length := by
  intro source hs ht
  rcases List.mem_append.mp hs with hc|hi
  · obtain ⟨_,_,he⟩ := List.mem_map.mp hc
    cases he
    contradiction
  · obtain ⟨index,hindex,heq⟩ := List.mem_map.mp hi
    rw [←heq]
    exact List.mem_range.mp hindex

/-- The true loaded work register consists of fair-bit zeros and an exact input
copy, while the original input positions are read-only. -/
theorem inputCopy_written (coinSlots inputSlots : List Unit) (state : ℕ → Bool)
    (index : ℕ) (hi : index < coinSlots.length+inputSlots.length) :
    BooleanProgram.run inputSlots.length (registerLoadOps (inputCopySources coinSlots inputSlots)) state
      (inputSlots.length+index)=if index < coinSlots.length then false else state (index-coinSlots.length) := by
  rw [registerLoadOps_value inputSlots.length _ (inputCopySources_valid coinSlots inputSlots) state index
    (by simpa only [inputCopySources_length] using hi)]
  unfold inputCopySources
  by_cases hc : index < coinSlots.length
  · rw [List.getElem_append_left (show index < (coinSlots.map (fun _ => (false,(0 : ℕ)))).length by simpa using hc)]
    simp [registerLoadValue,List.getElem_map,hc]
  · have hm : (coinSlots.map (fun _ => (false,0))).length ≤ index := by simp; omega
    rw [List.getElem_append_right hm]
    simp only [List.length_map,List.getElem_map,List.getElem_range,registerLoadValue,ite_true,if_neg hc]

@[fun_prop] theorem inputCopyGateWords_poly :
    Poly (fun x : List Unit × (List Unit × List Unit) => inputCopyGateWords x.1 x.2.1 x.2.2) := by
  unfold inputCopyGateWords
  fun_prop

theorem inputCopyGateWords_correct {total : ℕ} (slots coinSlots inputSlots : List Unit)
    (hn : inputSlots.length+(coinSlots.length+inputSlots.length) ≤ total)
    (hs : inputSlots.length+(coinSlots.length+inputSlots.length) ≤ slots.length) :
    inputCopyGateWords slots coinSlots inputSlots=
      (BooleanProgram.gates inputSlots.length (registerLoadOps (inputCopySources coinSlots inputSlots))
        (by simpa only [registerLoadOps_length,inputCopySources_length] using hn)).map BooleanGate.code :=
  registerLoadGateWords_correct slots inputSlots.length (inputCopySources coinSlots inputSlots)
    (inputCopySources_valid coinSlots inputSlots)
    (by simpa only [inputCopySources_length] using hn)
    (by simpa only [inputCopySources_length] using hs)

end InfoLossLAR.WorstCase

end P2MDyadicModule65

/- Helper module Solutions.AdvantageBridgeCopyPreparation. -/
section P2MDyadicModule66

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity TM2Boolean

namespace BooleanProgram

/-- A fresh program preserves every wire after its complete write interval. -/
theorem run_after (start : ℕ) (ops : List BooleanOp) (state : ℕ → Bool) (index : ℕ)
    (hi : start+ops.length ≤ index) : run start ops state index=state index := by
  induction ops generalizing start state with
  | nil => rfl
  | cons op rest ih =>
    change run (start+1) rest (op.assign start state) index=state index
    rw [ih (start+1) _ (by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi)]
    exact Function.update_of_ne (by simp only [List.length_cons] at hi; omega) _ _

end BooleanProgram

/-- The actual zero/copy program prepares coin-first work input while retaining
all original input wires and every later zero scratch wire. -/
theorem inputCopy_run (word : Str) (coins index : ℕ) :
    BooleanProgram.run word.length
      (registerLoadOps (inputCopySources (List.replicate coins ()) (List.replicate word.length ())))
      (wordExtension word) index=inputCopyResult word coins index := by
  by_cases hi : index < word.length
  · rw [BooleanProgram.run_below _ _ _ _ hi]
    simp [inputCopyResult,hi]
  · by_cases hm : index < word.length+coins+word.length
    · have hj : index-word.length < coins+word.length := by omega
      have h := inputCopy_written (List.replicate coins ()) (List.replicate word.length ())
        (wordExtension word) (index-word.length) (by simpa only [List.length_replicate] using hj)
      simp only [List.length_replicate,Nat.add_sub_of_le (by omega : word.length ≤ index)] at h
      rw [h]
      by_cases hc : index < word.length+coins
      · simp only [inputCopyResult,if_neg hi,if_pos hc,if_pos (by omega : index-word.length < coins)]
      · simp only [inputCopyResult,if_neg hi,if_neg hc,if_pos hm,if_neg (by omega : ¬index-word.length < coins)]
        rw [Nat.sub_sub]
    · rw [BooleanProgram.run_after _ _ _ _ (by
        simp only [registerLoadOps_length,inputCopySources_length,List.length_replicate]; omega)]
      rw [wordExtension_after word _ (by omega)]
      simp [inputCopyResult,hi,hm,show ¬index < word.length+coins by omega]

/-- The literal initial-copy Clifford+T circuit acts on the platform basis input
and produces precisely the retained-input, coin-zero, work-copy, scratch-zero basis. -/
theorem inputCopy_circuit_basis (word : Str) (coins extra : ℕ) :
    runLayered (compileReversible (booleanToReversible
      (BooleanProgram.gates word.length
        (registerLoadOps (inputCopySources (List.replicate coins ()) (List.replicate word.length ())))
        (by simp only [registerLoadOps_length,inputCopySources_length,List.length_replicate]; omega :
          word.length+(registerLoadOps (inputCopySources (List.replicate coins ())
            (List.replicate word.length ()))).length ≤ word.length+((coins+(word.length+extra))+1)))))
      (basisInput (a := coins+(word.length+extra)) (toBits word))=
        computationalBasis (fun index : Fin (word.length+((coins+(word.length+extra))+1)) =>
          inputCopyResult word coins index.val) := by
  rw [basisInput_eq_computationalBasis,wordExtension_basis]
  have h := BooleanProgram.circuit_basis
    (registerLoadOps (inputCopySources (List.replicate coins ()) (List.replicate word.length ())))
    (by simp only [registerLoadOps_length,inputCopySources_length,List.length_replicate]; omega :
      word.length+(registerLoadOps (inputCopySources (List.replicate coins ())
        (List.replicate word.length ()))).length ≤ word.length+((coins+(word.length+extra))+1))
    (registerLoadOps_valid _ _ (by simpa only [List.length_replicate] using
      (inputCopySources_valid (List.replicate coins ()) (List.replicate word.length ())))) (wordExtension word)
    (fun index hi _ => wordExtension_after word index hi)
  unfold computationalBasis
  simpa only [inputCopy_run] using h

end InfoLossLAR.WorstCase

end P2MDyadicModule66

/- Helper module Solutions.AdvantageBridgePreparedLoad. -/
section P2MDyadicModule67

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

theorem preparedLoadOps_valid {f : Str → Str} (P : PolyProgram id id f)
    (length : ℕ) (sources : List (Bool × ℕ))
    (hs : ∀ source∈sources,source.1=true → source.2 < length+((compiled P length).ops.length+1)) :
    BooleanProgram.Valid length (preparedLoadOps P length sources) := by
  classical
  rw [preparedLoadOps,BooleanProgram.valid_append]
  refine ⟨(machineProgram_valid (capacity_pos P length) P.machine.code P.machine.input P.machine.main
    P.machine.initial (P.time.eval length) length).1,?_⟩
  change (BooleanOp.constant false).Valid (length+(compiled P length).ops.length) ∧
    BooleanProgram.Valid (length+(compiled P length).ops.length+1) (registerLoadOps sources)
  constructor
  · simp [BooleanOp.Valid,BooleanOp.sources]
  · convert registerLoadOps_valid _ sources hs using 1  <;> omega

theorem preparedCoreBits_prefix {f : Str → Str} (P : PolyProgram id id f) (word : Str) (index : ℕ)
    (hi : index < word.length+((compiled P word.length).ops.length+1)) :
    preparedCoreBits P word index=generatedQueryBits P word index := by
  unfold preparedCoreBits generatedQueryBits selectorBitsExtension result
  simp only [dif_pos hi,Fin.val_mk]
  by_cases he : index=word.length+(compiled P word.length).ops.length
  · subst index
    rw [Function.update_self,BooleanProgram.run_after _ _ _ _ le_rfl,
      wordExtension_after word _ (by omega)]
  · exact Function.update_of_ne he _ _

/-- The combined true preprocessing/load program preserves every real machine
output flag/payload wire, including its actual terminal zero workspace bit. -/
theorem preparedLoadOps_prefix {f : Str → Str} (P : PolyProgram id id f) (word : Str)
    (sources : List (Bool × ℕ)) (index : ℕ)
    (hi : index < word.length+((compiled P word.length).ops.length+1)) :
    BooleanProgram.run word.length (preparedLoadOps P word.length sources) (wordExtension word) index=
      generatedQueryBits P word index := by
  rw [preparedLoadOps,BooleanProgram.run_append]
  simp only [BooleanProgram.run,BooleanOp.assign,BooleanOp.eval]
  rw [BooleanProgram.run_below _ _ _ _ (by omega)]
  exact preparedCoreBits_prefix P word index hi

/-- Every D-load destination gets exactly the true previously computed query
output value at its emitted pointer, with all non-copy positions zero. -/
theorem preparedLoadOps_written {f : Str → Str} (P : PolyProgram id id f) (word : Str)
    (sources : List (Bool × ℕ))
    (hs : ∀ source∈sources,source.1=true → source.2 < word.length+((compiled P word.length).ops.length+1))
    (index : ℕ) (hi : index < sources.length) :
    BooleanProgram.run word.length (preparedLoadOps P word.length sources) (wordExtension word)
      (word.length+((compiled P word.length).ops.length+1)+index)=
        registerLoadValue sources[index] (generatedQueryBits P word) := by
  rw [preparedLoadOps,BooleanProgram.run_append]
  simp only [BooleanProgram.run,BooleanOp.assign,BooleanOp.eval]
  have he : word.length+(compiled P word.length).ops.length+1=
      word.length+((compiled P word.length).ops.length+1) := by omega
  rw [he]
  change BooleanProgram.run _ (registerLoadOps sources) (preparedCoreBits P word) _=_
  rw [registerLoadOps_value _ sources hs _ index hi]
  unfold registerLoadValue
  cases ht : sources[index].1
  · simp
  · simp only [ite_true]
    exact preparedCoreBits_prefix P word _ (hs sources[index] (List.getElem_mem hi) ht)

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule67

/- Helper module Solutions.AdvantageBridgeBodyCodeCapture. -/
section P2MDyadicModule68

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem readRawBooleanWord_poly : Poly readRawBooleanWord := by
  have hr : Poly (fun xs : Str => (readBooleanInstruction xs).1) :=
    Poly.comp Poly.fst readBooleanInstruction_poly
  have hn : Poly (fun xs : Str => xs.length-(readBooleanInstruction xs).1.length) :=
    Poly.comp Poly.nat_sub (Poly.pair Poly.list_length (Poly.comp Poly.list_length hr))
  have hc : Poly (fun xs : Str => xs.take (xs.length-(readBooleanInstruction xs).1.length)) :=
    Poly.comp (f := fun x : Str × ℕ => x.1.take x.2)
      (g := fun xs : Str => (xs,xs.length-(readBooleanInstruction xs).1.length))
      parser_take_poly (Poly.pair Poly.identity hn)
  exact Poly.pair hr hc

theorem readRawBooleanWord_rest_length (xs : Str) : (readRawBooleanWord xs).1.length ≤ xs.length :=
  readBooleanInstruction_rest_length xs

theorem readRawBooleanWord_append {n : ℕ} (gate : BooleanGate n) (suffix : Str) :
    readRawBooleanWord (gate.code++suffix)=(suffix,gate.code) := by
  unfold readRawBooleanWord
  rw [readBooleanInstruction_append]
  simp only [List.length_append,Nat.add_sub_cancel_right,List.take_left]

@[fun_prop] theorem readRawBooleanWords_poly : Poly readRawBooleanWords :=
  readList_poly readRawBooleanWord readRawBooleanWord_poly readRawBooleanWord_rest_length

theorem readRawBooleanWords_append {n : ℕ} (gates : List (BooleanGate n)) (suffix : Str) :
    readRawBooleanWords (encStr (gates.map BooleanGate.code)++suffix)=(suffix,gates.map BooleanGate.code) :=
  readList_append_mapped readRawBooleanWord BooleanGate.code BooleanGate.code readRawBooleanWord_append gates suffix

@[fun_prop] theorem readRawBooleanFamilyWords_poly : Poly readRawBooleanFamilyWords := by
  have hr : Poly (fun xs : Str => (readUnary xs).2) := Poly.comp Poly.snd readUnary_poly
  have ht : Poly (fun xs : Str => (readUnary ((readUnary xs).2)).2) :=
    Poly.comp (f := fun xs : Str => (readUnary xs).2) (g := fun xs : Str => (readUnary xs).2) hr hr
  have hp : Poly (fun xs : Str => readRawBooleanWords ((readUnary ((readUnary xs).2)).2)) :=
    Poly.comp (f := readRawBooleanWords) (g := fun xs : Str => (readUnary ((readUnary xs).2)).2)
      readRawBooleanWords_poly ht
  exact Poly.comp (f := fun x : Str × List Str => x.2)
    (g := fun xs : Str => readRawBooleanWords ((readUnary ((readUnary xs).2)).2)) Poly.snd hp

theorem readRawBooleanFamilyWords_code (F : BooleanFamily) (n : ℕ) :
    readRawBooleanFamilyWords (F.code n)=(F.gates n).map BooleanGate.code := by
  unfold readRawBooleanFamilyWords BooleanFamily.code
  simp only [List.append_assoc,readUnary_append]
  have h := readRawBooleanWords_append (F.gates n) []
  simpa only [List.append_nil] using congrArg Prod.snd h

namespace BooleanProgram

/-- Exact finite-gate append for the actual contiguous fresh assignment program. -/
theorem gates_append {total start : ℕ} (first second : List BooleanOp)
    (h : start+(first++second).length ≤ total) :
    gates start (first++second) h=
      gates start first (by simp only [List.length_append] at h; omega) ++
        gates (start+first.length) second (by simpa only [List.length_append,Nat.add_assoc] using h) := by
  induction first generalizing start with
  | nil => simp only [List.nil_append,gates,List.length_nil,Nat.add_zero]
  | cons op rest ih =>
    simp only [List.cons_append,gates,List.length_cons]
    congr 1
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (start := start+1) (by simp only [List.length_cons,List.length_append] at h ⊢; omega)

/-- Actual serialized instructions depend on wire values, not the ambient
finite-register bound; both gate lists are genuine valid instantiations. -/
theorem gateCodes_width_independent {left right start : ℕ} (ops : List BooleanOp)
    (hl : start+ops.length ≤ left) (hr : start+ops.length ≤ right) (hv : Valid start ops) :
    (gates start ops hl).map BooleanGate.code=(gates start ops hr).map BooleanGate.code := by
  let slots := List.replicate (start+ops.length) ()
  have hs : start+ops.length ≤ slots.length := by simp [slots]
  exact (TM2Boolean.RPN.instructionWords_gates slots start ops hl hv hs).symm.trans
    (TM2Boolean.RPN.instructionWords_gates slots start ops hr hv hs)

end BooleanProgram

namespace TM2Boolean.PolyProgramCircuit

/-- Actual compiler gate words can be reused in the larger prep/D/selector
register while retaining the exact finite Boolean program semantics. -/
theorem compilerRawWords_correct {f : Str → Str} (P : PolyProgram id id f) (n total : ℕ)
    (hn : n+(compiled P n).ops.length ≤ total) :
    readRawBooleanFamilyWords (descriptionGenerator P (unary n))=
      (BooleanProgram.gates n (compiled P n).ops hn).map BooleanGate.code := by
  classical
  rw [descriptionGenerator_code,readRawBooleanFamilyWords_code]
  change (BooleanProgram.gates n (compiled P n).ops _).map BooleanGate.code=_
  exact BooleanProgram.gateCodes_width_independent _ _ hn
    (machineProgram_valid (capacity_pos P n) P.machine.code P.machine.input P.machine.main P.machine.initial
      (P.time.eval n) n).1

end TM2Boolean.PolyProgramCircuit

end InfoLossLAR.WorstCase

end P2MDyadicModule68

/- Helper module Solutions.AdvantageBridgeBodyFamily. -/
section P2MDyadicModule69

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary

theorem castBodyCircuit_depth {left right : ℕ} (h : left=right) (circuit : Layered left) :
    depth (castBodyCircuit h circuit)=depth circuit := by cases h; rfl

theorem castBodyCircuit_wellFormed {left right : ℕ} (h : left=right) (circuit : Layered left)
    (hc : ∀ layer∈circuit,LayerOk layer) : ∀ layer∈castBodyCircuit h circuit,LayerOk layer := by
  cases h; exact hc

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule69

/- Helper module Solutions.AdvantageBridgeUniformDBuilder. -/
section P2MDyadicModule70

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 Integration9_9.TM2StockLists

/-- A real native description builder may consume the original input and all
true D descriptions through any fixed polynomial length. The resulting raw
string function is computed by an actual stock TM2 program under exactly the
original Uniform D hypothesis, including arbitrary internal callee alphabets. -/
theorem uniformDTable_builder_polyTime (D : Family) (hD : Uniform D) (padding : Polynomial ℕ)
    (builder : Str × List (Str × Str) → Str) (hbuilder : Poly builder) :
    PolyTimeComputable (fun word : Str => builder (word,describedQueryBlocks D (padding.eval word.length))) := by
  obtain ⟨source,hsource,hcorrect⟩ := hD
  obtain ⟨table⟩ := generatedBundleDescriptions_stock source hsource padding
  obtain ⟨quotedTable⟩ := TM2Composition.comp BooleanLists.unpackProgram.stock table
  obtain ⟨paired⟩ := stock_pairWithInput quotedTable
  obtain ⟨built⟩ := TM2Composition.comp paired hbuilder.program.stock
  obtain ⟨output⟩ := TM2Composition.comp built BooleanLists.unpackProgram.stock
  obtain ⟨whole⟩ := TM2Composition.comp BooleanLists.packProgram.stock output
  refine ⟨congrProgram whole _ ?_⟩
  intro word
  simp only [Function.comp_apply,id_eq]
  rw [generatedBundleDescriptions_correct D source hcorrect]

end InfoLossLAR.WorstCase

end P2MDyadicModule70

/- Helper module Solutions.AdvantageBridgeBodyBooleanEmission. -/
section P2MDyadicModule71

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.BooleanProgram

open QAlgorithms.Complexity

theorem gateCodes_start_congr {total left right : ℕ} (he : left=right) (ops : List BooleanOp)
    (hl : left+ops.length ≤ total) (hr : right+ops.length ≤ total) :
    (gates left ops hl).map BooleanGate.code=(gates right ops hr).map BooleanGate.code := by cases he; rfl

end InfoLossLAR.WorstCase.BooleanProgram

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime TM2PlatformSerialization TM2Boolean.RPN

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule71

/- Helper module Solutions.AdvantageBridgeBodyDEmission. -/
section P2MDyadicModule72

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

theorem leftCircuit_instructionWords {n m : ℕ} (circuit : Layered n) :
    (leftCircuit (m := m) circuit).map (List.map encInstr)=circuit.map (List.map encInstr) := by
  have hg (gate : Instr n) : encInstr (leftInstruction (m := m) gate)=encInstr gate := by cases gate <;> rfl
  simp only [leftCircuit,List.map_map,Function.comp_def,hg]

theorem rightCircuit_instructionWords_congr {n : ℕ} (left right : ℕ) (he : left=right) (circuit : Layered n) :
    (rightCircuit (n := left) circuit).map (List.map encInstr)=
      (rightCircuit (n := right) circuit).map (List.map encInstr) := by cases he; rfl

end InfoLossLAR.WorstCase

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2PlatformSerialization

theorem castBodyCircuit_instructionWords {left right : ℕ} (he : left=right) (circuit : Layered left) :
    (castBodyCircuit he circuit).map (List.map encInstr)=circuit.map (List.map encInstr) := by cases he; rfl

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule72

/- Helper module Solutions.AdvantageBridgeBodyUniform. -/
section P2MDyadicModule73

set_option autoImplicit false

set_option maxHeartbeats 500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem readFamilyCircuitLayers_poly : Poly readFamilyCircuitLayers := by
  have hr : Poly (fun xs : Str => (readUnary xs).2) := Poly.comp Poly.snd readUnary_poly
  have ht : Poly (fun xs : Str => (readUnary ((readUnary xs).2)).2) :=
    Poly.comp (f := fun xs : Str => (readUnary xs).2) (g := fun xs : Str => (readUnary xs).2) hr hr
  have hp : Poly (fun xs : Str => readCircuitLayers ((readUnary ((readUnary xs).2)).2)) :=
    Poly.comp readCircuitLayers_poly ht
  exact Poly.comp (f := fun x : Str × List (List Str) => x.2)
    (g := fun xs : Str => readCircuitLayers ((readUnary ((readUnary xs).2)).2)) Poly.snd hp

theorem readFamilyCircuitLayers_correct (F : Family) (n : ℕ) :
    readFamilyCircuitLayers (encFamilyAt F n)=(F.circ n).map (List.map encInstr) := by
  unfold readFamilyCircuitLayers encFamilyAt
  simp only [List.append_assoc,readUnary_append]
  have h := readCircuitLayers_append (F.circ n) []
  simpa only [List.append_nil] using congrArg Prod.snd h

end InfoLossLAR.WorstCase

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2PlatformSerialization InfoLossLAR.WorstCase.TM2Boolean.RPN

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule73

/- Helper module Solutions.AdvantageBridgeGenericBodyQuery. -/
section P2MDyadicModule74

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBody

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.LARCoinLayout

theorem bodyQueryOutput_capacity (Q : QueryProgram) (n : ℕ) :
    2 * Q.padding.eval n + 1 < capacity (bodyQueryProgram Q) n := by
  have h := actualOutput_length_lt_capacity (bodyQueryProgram Q) (unary n)
  change (Q.f (unary n)).length < _ at h
  rw [Q.output_length] at h
  simpa only [unary,List.length_replicate] using h

@[fun_prop] theorem bodyFlagAddresses_poly (Q : QueryProgram) : Poly (bodyFlagAddresses Q) := by
  unfold bodyFlagAddresses
  fun_prop

@[fun_prop] theorem bodyPayloadAddresses_poly (Q : QueryProgram) : Poly (bodyPayloadAddresses Q) := by
  unfold bodyPayloadAddresses
  fun_prop

theorem bodyPayloadAddresses_length (Q : QueryProgram) (word : Str) :
    (bodyPayloadAddresses Q word).length = Q.padding.eval word.length := by
  simp only [bodyPayloadAddresses,generatedAddressRange,List.length_map,List.length_range,queryWireSlots_length]

theorem bodyPayloadAddresses_valid (Q : QueryProgram) (n : ℕ) :
    ∀ address ∈ bodyPayloadAddresses Q (unary n),
      address < n + ((compiled (bodyQueryProgram Q) n).ops.length + 1) := by
  intro address ha
  apply generatedAddressRange_bounded (bodyQueryProgram Q) n
    (queryWireSlots Q.padding (unary n)) ((queryWireSlots Q.padding (unary n)).length + 1) _ address ha
  have h := bodyQueryOutput_capacity Q n
  simp only [queryWireSlots_length,unary,List.length_replicate]
  omega

theorem bodyFlagAddresses_valid (Q : QueryProgram) (n : ℕ) :
    ∀ address ∈ bodyFlagAddresses Q (unary n),
      address < n + ((compiled (bodyQueryProgram Q) n).ops.length + 1) := by
  intro address ha
  apply generatedAddressRange_bounded (bodyQueryProgram Q) n
    (queryWireSlots Q.padding (unary n) ++ [()]) 0 _ address ha
  have h := bodyQueryOutput_capacity Q n
  simp only [zero_add,List.length_append,List.length_singleton,queryWireSlots_length,unary,List.length_replicate]
  omega

theorem bodyDLoadSources_valid (Q : QueryProgram) (D : Family) (n : ℕ) :
    ∀ source ∈ dBundleLoadSources (bodyPayloadAddresses Q (unary n))
      (describedQueryBlocks D (Q.padding.eval n)), source.1 = true →
        source.2 < n + ((compiled (bodyQueryProgram Q) n).ops.length + 1) :=
  dBundleLoadSources_actual_valid _ D _ _
    (by simp only [bodyPayloadAddresses_length,unary,List.length_replicate])
    (bodyPayloadAddresses_valid Q n)

end Integration9_9.GenericBody

end

end P2MDyadicModule74

/- Helper module Solutions.AdvantageBridgeGenericBodyLayout. -/
section P2MDyadicModule75

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBody

open Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime TM2PlatformSerialization

@[fun_prop] theorem bodyPreAncSlots_poly (Q : QueryProgram) :
    Poly (bodyPreAncSlots Q) := by
  unfold bodyPreAncSlots
  fun_prop

@[fun_prop] theorem bodyPreSlots_poly (Q : QueryProgram) : Poly (bodyPreSlots Q) := by
  unfold bodyPreSlots
  fun_prop

theorem bodyPreSlots_length (Q : QueryProgram) (n : ℕ) :
    (bodyPreSlots Q (unary n)).length=n+((compiled (bodyQueryProgram Q) n).ops.length+1) := by
  simp only [bodyPreSlots,List.length_append,List.length_map,List.length_singleton,bodyPreAncSlots_length]
  simp only [unary,List.length_replicate]
  omega

@[fun_prop] theorem bodyDBundleSlots_poly : Poly bodyDBundleSlots := by
  unfold bodyDBundleSlots
  fun_prop

@[fun_prop] theorem bodySelectorChoices_poly (Q : QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => bodySelectorChoices Q x.1 x.2) := by
  unfold bodySelectorChoices
  fun_prop

theorem bodySelectorChoices_valid (Q : QueryProgram) (D : Family) (n : ℕ) :
    ∀ choice∈bodySelectorChoices Q (unary n) (describedQueryBlocks D (Q.padding.eval n)),
      choice.1 < (bodyPreSlots Q (unary n)).length+
          (bodyDBundleSlots (describedQueryBlocks D (Q.padding.eval n))).length ∧
      choice.2 < (bodyPreSlots Q (unary n)).length+
          (bodyDBundleSlots (describedQueryBlocks D (Q.padding.eval n))).length := by
  intro choice hc
  obtain ⟨hf,ho⟩ := List.of_mem_zip hc
  have hflag := bodyFlagAddresses_valid Q n choice.1 hf
  rw [←bodyPreSlots_length Q n] at hflag
  obtain ⟨token,ht,he⟩ := List.mem_map.mp ho
  have hout := emittedDOutputAddresses_valid D (Q.padding.eval n) [] (inputWidth token)
    (List.mem_map.mpr ⟨token,ht,rfl⟩)
  rw [bodyDBundleSlots_length D _ []]
  constructor
  · omega
  · rw [←he]
    omega

@[fun_prop] theorem bodyAncSlots_poly (Q : QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => bodyAncSlots Q x.1 x.2) := by
  unfold bodyAncSlots
  fun_prop

@[fun_prop] theorem bodyAllSlots_poly (Q : QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => bodyAllSlots Q x.1 x.2) := by
  unfold bodyAllSlots
  fun_prop

theorem bodyAllSlots_length (Q : QueryProgram) (word : Str) (descriptions : List (Str × Str)) :
    (bodyAllSlots Q word descriptions).length=
      (bodyPreSlots Q word).length+(bodyDBundleSlots descriptions).length+
        4*(bodySelectorChoices Q word descriptions).length+1 := by
  simp only [bodyAllSlots,bodyAncSlots,bodyPreSlots,List.length_append,List.length_map,List.length_singleton,
    multiSelectorScratch_length]
  omega

end Integration9_9.GenericBody

end

end P2MDyadicModule75

/- Helper module Solutions.AdvantageBridgeGenericBodyFamily. -/
section P2MDyadicModule76

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBody

open Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary

theorem bodyPrepared_valid (Q : QueryProgram) (D : Family) (n : ℕ) :
    BooleanProgram.Valid n (preparedLoadOps (bodyQueryProgram Q) n
      (bodySources Q D n)) :=
  preparedLoadOps_valid _ _ _ (bodyDLoadSources_valid Q D n)

theorem castBodyCircuit_depth {left right : ℕ} (h : left=right) (circuit : Layered left) :
    depth (castBodyCircuit h circuit)=depth circuit := by cases h; rfl

theorem castBodyCircuit_wellFormed {left right : ℕ} (h : left=right) (circuit : Layered left)
    (hc : ∀ layer∈circuit,LayerOk layer) : ∀ layer∈castBodyCircuit h circuit,LayerOk layer := by
  cases h; exact hc

theorem bodyDCircuit_wellFormed (Q : QueryProgram) (D : Family)
    (hD : WellFormed D) (n : ℕ) : ∀ layer∈bodyDCircuit Q D n,LayerOk layer :=
  castBodyCircuit_wellFormed _ _ (leftCircuit_wellFormed _
    (rightCircuit_wellFormed _ (queryBlocks_wellFormed D hD (Q.padding.eval n) [])))

theorem bodyFamily_wellFormed (Q : QueryProgram) (D : Family)
    (hD : WellFormed D) : WellFormed (bodyFamily Q D) := by
  intro n layer hl
  simp only [bodyFamily,bodyCircuit,List.mem_append] at hl
  rcases hl with (hp|hd)|hs
  · exact compileReversible_wellFormed _ layer hp
  · exact bodyDCircuit_wellFormed Q D hD n layer hd
  · exact compileReversible_wellFormed _ layer hs

end Integration9_9.GenericBody

end

end P2MDyadicModule76

/- Helper module Solutions.AdvantageBridgeGenericBodyResources. -/
section P2MDyadicModule77

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBody

open Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary

theorem bodyAnc_le (Q : QueryProgram) (D : Family) (Dbound : Polynomial ℕ)
    (hanc : ∀ n,D.anc n ≤ Dbound.eval n) (n : ℕ) :
    bodyAnc Q D n ≤ (bodyAncPolynomial Q Dbound).eval n := by
  have hp := ancilla_bound (bodyQueryProgram Q) n
  have hd := queryBlocks_width_le D Dbound hanc (Q.padding.eval n) []
  rw [bodyAnc_formula]
  simp only [bodyAncPolynomial,bodyDWidthPolynomial,eval_add,eval_mul,eval_one,eval_ofNat,eval_comp]
  change _ ≤ _
  dsimp only [bodyDWidth]
  omega

theorem bodyPrepared_depth (Q : QueryProgram) (D : Family) (n : ℕ) :
    depth (compileReversible (booleanToReversible (bodyPreparedGates Q D n))) ≤ 
      74*((compiled (bodyQueryProgram Q) n).ops.length+1+bodyDWidth Q D n) := by
  have h := BooleanProgram.circuit_depth
    (preparedLoadOps (bodyQueryProgram Q) n (bodySources Q D n))
    (bodyPrepared_bound Q D n)
  unfold bodyPreparedGates
  exact h.trans (by rw [preparedLoadOps_length,bodySources_length])

theorem bodySelector_depth (Q : QueryProgram) (D : Family) (n : ℕ) :
    depth (compileReversible (booleanToReversible (bodySelectorGates Q D n))) ≤ 296*(Q.padding.eval n+1) := by
  have h := BooleanProgram.circuit_depth
    (multiSelectorOps (bodyPreWidth Q n+bodyDWidth Q D n) 0
      (bodyChoices Q D n))
    (by simpa only [multiSelectorOps_length] using bodySelected_bound Q D n)
  unfold bodySelectorGates
  exact h.trans (by rw [multiSelectorOps_length,bodyChoices_length]; omega)

theorem bodyD_depth (Q : QueryProgram) (D : Family) (Dbound : Polynomial ℕ)
    (hdepth : ∀ n,depth (D.circ n) ≤ Dbound.eval n) (n : ℕ) :
    depth (bodyDCircuit Q D n) ≤ (Q.padding.eval n+1)*Dbound.eval (Q.padding.eval n) := by
  unfold bodyDCircuit
  rw [castBodyCircuit_depth,leftCircuit_depth,rightCircuit_depth]
  exact queryBlocks_depth_le D Dbound hdepth (Q.padding.eval n) []

theorem bodyCircuit_depth_le (Q : QueryProgram) (D : Family) (Dbound : Polynomial ℕ)
    (hdepth : ∀ n,depth (D.circ n) ≤ Dbound.eval n) (hanc : ∀ n,D.anc n ≤ Dbound.eval n) (n : ℕ) :
    depth (bodyCircuit Q D n) ≤ (bodyDepthPolynomial Q Dbound).eval n := by
  have hp := ancilla_bound (bodyQueryProgram Q) n
  have hd := queryBlocks_width_le D Dbound hanc (Q.padding.eval n) []
  have hprep := bodyPrepared_depth Q D n
  have hselect := bodySelector_depth Q D n
  have hddepth := bodyD_depth Q D Dbound hdepth n
  simp only [bodyCircuit,depth,List.length_append]
  simp only [depth,bodyDWidth] at hprep hselect hddepth
  simp only [bodyDepthPolynomial,bodyDWidthPolynomial,eval_add,eval_mul,eval_one,eval_ofNat,eval_comp]
  omega

/-- The concrete full preprocessing/D/selector body has a genuine polynomial
ancilla/depth bound whenever the original D does. -/
theorem bodyFamily_polyBounded (Q : QueryProgram) (D : Family)
    (hD : PolyBounded D) : PolyBounded (bodyFamily Q D) := by
  obtain ⟨Dbound,hdepth,hanc⟩ := hD
  refine ⟨bodyDepthPolynomial Q Dbound+bodyAncPolynomial Q Dbound,?_,?_⟩
  · intro n
    have h := bodyCircuit_depth_le Q D Dbound hdepth hanc n
    change depth (bodyCircuit Q D n) ≤ _
    simp only [eval_add]
    omega
  · intro n
    have h := bodyAnc_le Q D Dbound hanc n
    change bodyAnc Q D n ≤ _
    simp only [eval_add]
    omega

end Integration9_9.GenericBody

end

end P2MDyadicModule77

/- Helper module Solutions.AdvantageBridgeGenericBodyBooleanEmission. -/
section P2MDyadicModule78

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBody

open Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime TM2PlatformSerialization TM2Boolean.RPN

theorem bodyAllSlots_actual_length (Q : QueryProgram) (D : Family) (n : ℕ) :
    (bodyAllSlots Q (unary n) (describedQueryBlocks D (Q.padding.eval n))).length=
      bodyWidth Q D n := by
  rw [bodyAllSlots_length,bodyPreSlots_length,bodyDBundleSlots_length D _ [],bodySelectorChoices_length,
    bodyWidth_formula]
  rfl

@[fun_prop] theorem bodyZeroWord_poly (Q : QueryProgram) : Poly (bodyZeroWord Q) := by
  unfold bodyZeroWord
  fun_prop

theorem bodyZeroWord_correct (Q : QueryProgram) (n : ℕ) :
    bodyZeroWord Q (unary n)=
      encNat 0++encNat (n+(compiled (bodyQueryProgram Q) n).ops.length) := by
  simp only [bodyZeroWord,lengthToken_eq,List.length_append,List.length_map,bodyPreAncSlots_length]
  simp only [unary,List.length_replicate]

@[fun_prop] theorem bodyPreparedWords_poly (Q : QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => bodyPreparedWords Q x.1 x.2) := by
  unfold bodyPreparedWords
  fun_prop

theorem bodyPreparedWords_correct (Q : QueryProgram) (D : Family) (n : ℕ) :
    bodyPreparedWords Q (unary n) (describedQueryBlocks D (Q.padding.eval n))=
      (bodyPreparedGates Q D n).map BooleanGate.code := by
  let P := bodyQueryProgram Q
  let total := bodyWidth Q D n
  let sources := bodySources Q D n
  have hp : n+(compiled P n).ops.length ≤ total := by
    have h := bodyPrepared_bound Q D n
    rw [preparedLoadOps_length] at h
    dsimp only [P,total]
    omega
  have hstart : (bodyPreSlots Q (unary n)).length=n+(compiled P n).ops.length+1 := by
    rw [bodyPreSlots_length]; dsimp only [P]; omega
  have hd : (bodyPreSlots Q (unary n)).length+sources.length ≤ total := by
    rw [bodyPreSlots_length]
    dsimp only [sources,total]
    rw [bodySources_length,bodyWidth_formula]
    dsimp only [bodyPreWidth,P]
    omega
  have hold : n+(compiled P n).ops.length+1+(registerLoadOps sources).length ≤ total := by
    rw [registerLoadOps_length]
    rw [hstart] at hd
    exact hd
  have hs : ∀ source∈sources,source.1=true → source.2 < (bodyPreSlots Q (unary n)).length := by
    rw [bodyPreSlots_length]
    exact bodyDLoadSources_valid Q D n
  have hload := registerLoadGateWords_correct
    (bodyAllSlots Q (unary n) (describedQueryBlocks D (Q.padding.eval n)))
    (bodyPreSlots Q (unary n)).length sources hs hd
    (by rw [bodyAllSlots_actual_length]; exact hd)
  have hload' :
      registerLoadGateWords (bodyAllSlots Q (unary n) (describedQueryBlocks D (Q.padding.eval n)))
        (bodyPreSlots Q (unary n)).length sources=
      (BooleanProgram.gates (n+(compiled P n).ops.length+1) (registerLoadOps sources) hold).map BooleanGate.code :=
    hload.trans (BooleanProgram.gateCodes_start_congr hstart (registerLoadOps sources) _ hold)
  unfold bodyPreparedWords
  change readRawBooleanFamilyWords (descriptionGenerator P (unary n))++[bodyZeroWord Q (unary n)]++
    registerLoadGateWords _ _ sources=_
  rw [compilerRawWords_correct P n total hp,bodyZeroWord_correct,hload']
  unfold bodyPreparedGates preparedLoadOps
  rw [BooleanProgram.gates_append]
  simp only [List.map_append,BooleanProgram.gates,List.map_cons,BooleanGate.code,Bool.false_eq_true,ite_false,
    List.singleton_append,List.append_assoc]
  rfl

@[fun_prop] theorem bodySelectorWords_poly (Q : QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => bodySelectorWords Q x.1 x.2) := by
  unfold bodySelectorWords
  fun_prop

theorem bodySelectorWords_correct (Q : QueryProgram) (D : Family) (n : ℕ) :
    bodySelectorWords Q (unary n) (describedQueryBlocks D (Q.padding.eval n))=
      (bodySelectorGates Q D n).map BooleanGate.code := by
  unfold bodySelectorWords
  rw [bodyPreSlots_length,bodyDBundleSlots_length D _ []]
  change multiSelectorGateWords _ (bodyPreWidth Q n+bodyDWidth Q D n) 0
    (bodyChoices Q D n)=_
  apply multiSelectorGateWords_correct
  · unfold bodyPreWidth; omega
  · have h := bodySelectorChoices_valid Q D n
    rw [bodyPreSlots_length,bodyDBundleSlots_length D _ []] at h
    exact h
  · exact bodySelected_bound Q D n
  · rw [bodyAllSlots_actual_length]
    exact bodySelected_bound Q D n

end Integration9_9.GenericBody

end

end P2MDyadicModule78

/- Helper module Solutions.AdvantageBridgeGenericBodyDEmission. -/
section P2MDyadicModule79

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBody

open Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2PlatformSerialization

theorem castBodyCircuit_instructionWords {left right : ℕ} (he : left=right) (circuit : Layered left) :
    (castBodyCircuit he circuit).map (List.map encInstr)=circuit.map (List.map encInstr) := by cases he; rfl

@[fun_prop] theorem bodyDWordLayers_poly (Q : QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => bodyDWordLayers Q x.1 x.2) := by
  unfold bodyDWordLayers
  fun_prop

theorem bodyDWordLayers_correct (Q : QueryProgram) (D : Family) (n : ℕ) :
    bodyDWordLayers Q (unary n) (describedQueryBlocks D (Q.padding.eval n))=
      (bodyDCircuit Q D n).map (List.map encInstr) := by
  unfold bodyDWordLayers
  rw [describedQueryBlocks_frames D _ [],bundleCircuitWordLayers_correct,shiftCircuitWords_correct]
  unfold bodyDCircuit
  rw [castBodyCircuit_instructionWords,leftCircuit_instructionWords]
  apply rightCircuit_instructionWords_congr
  simp only [List.length_map]
  exact bodyPreSlots_length Q n

end Integration9_9.GenericBody

end

end P2MDyadicModule79

/- Helper module Solutions.AdvantageBridgeGenericBodyUniform. -/
section P2MDyadicModule80

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBody

open Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2PlatformSerialization InfoLossLAR.WorstCase.TM2Boolean.RPN

@[fun_prop] theorem bodyOutputWord_poly (Q : QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => bodyOutputWord Q x.1 x.2) := by
  unfold bodyOutputWord
  fun_prop

theorem bodyOutputWord_correct (Q : QueryProgram) (D : Family) (n : ℕ) :
    bodyOutputWord Q (unary n) (describedQueryBlocks D (Q.padding.eval n))=
      encNat (bodyOutput Q D n).val := by
  unfold bodyOutputWord
  rw [bodyPreSlots_length,bodyDBundleSlots_length D _ [],multiSelectorFinalIndex_eq]
  change boundedNat _ (bodyOutput Q D n).val=_
  apply boundedNat_eq
  rw [bodyAllSlots_actual_length]
  exact (bodyOutput Q D n).isLt.le

@[fun_prop] theorem bodyPreparedBooleanDescription_poly (Q : QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => bodyPreparedBooleanDescription Q x.1 x.2) := by
  unfold bodyPreparedBooleanDescription
  fun_prop

theorem bodyPreparedBooleanDescription_correct (Q : QueryProgram) (D : Family) (n : ℕ) :
    bodyPreparedBooleanDescription Q (unary n) (describedQueryBlocks D (Q.padding.eval n))=
      (bodyPreparedBooleanFamily Q D).code n := by
  unfold bodyPreparedBooleanDescription
  rw [lengthToken_eq,bodyOutputWord_correct,bodyPreparedWords_correct,serializeWords_eq]
  rfl

@[fun_prop] theorem bodySelectorBooleanDescription_poly (Q : QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => bodySelectorBooleanDescription Q x.1 x.2) := by
  unfold bodySelectorBooleanDescription
  fun_prop

theorem bodySelectorBooleanDescription_correct (Q : QueryProgram) (D : Family) (n : ℕ) :
    bodySelectorBooleanDescription Q (unary n) (describedQueryBlocks D (Q.padding.eval n))=
      (bodySelectorBooleanFamily Q D).code n := by
  unfold bodySelectorBooleanDescription
  rw [lengthToken_eq,bodyOutputWord_correct,bodySelectorWords_correct,serializeWords_eq]
  rfl

@[fun_prop] theorem bodyPreparedQuantumDescription_poly (Q : QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => bodyPreparedQuantumDescription Q x.1 x.2) := by
  unfold bodyPreparedQuantumDescription
  fun_prop

theorem bodyPreparedQuantumDescription_correct (Q : QueryProgram) (D : Family) (n : ℕ) :
    bodyPreparedQuantumDescription Q (unary n) (describedQueryBlocks D (Q.padding.eval n))=
      encFamilyAt (bodyPreparedBooleanFamily Q D).reversible.compile n := by
  unfold bodyPreparedQuantumDescription
  rw [bodyPreparedBooleanDescription_correct,compileBooleanDescription_code,compileReversibleDescription_code]

@[fun_prop] theorem bodySelectorQuantumDescription_poly (Q : QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => bodySelectorQuantumDescription Q x.1 x.2) := by
  unfold bodySelectorQuantumDescription
  fun_prop

theorem bodySelectorQuantumDescription_correct (Q : QueryProgram) (D : Family) (n : ℕ) :
    bodySelectorQuantumDescription Q (unary n) (describedQueryBlocks D (Q.padding.eval n))=
      encFamilyAt (bodySelectorBooleanFamily Q D).reversible.compile n := by
  unfold bodySelectorQuantumDescription
  rw [bodySelectorBooleanDescription_correct,compileBooleanDescription_code,compileReversibleDescription_code]

attribute [local irreducible] bodyPreparedQuantumDescription bodySelectorQuantumDescription bodyDWordLayers

@[fun_prop] theorem bodyQuantumWordLayers_poly (Q : QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => bodyQuantumWordLayers Q x.1 x.2) := by
  have hp : Poly (fun x : Str × List (Str × Str) =>
      readFamilyCircuitLayers (bodyPreparedQuantumDescription Q x.1 x.2)) :=
    Poly.comp (f := readFamilyCircuitLayers)
      (g := fun x : Str × List (Str × Str) => bodyPreparedQuantumDescription Q x.1 x.2)
      readFamilyCircuitLayers_poly (bodyPreparedQuantumDescription_poly Q)
  have hs : Poly (fun x : Str × List (Str × Str) =>
      readFamilyCircuitLayers (bodySelectorQuantumDescription Q x.1 x.2)) :=
    Poly.comp (f := readFamilyCircuitLayers)
      (g := fun x : Str × List (Str × Str) => bodySelectorQuantumDescription Q x.1 x.2)
      readFamilyCircuitLayers_poly (bodySelectorQuantumDescription_poly Q)
  have hd := bodyDWordLayers_poly Q
  have htail : Poly (fun x : Str × List (Str × Str) => bodyDWordLayers Q x.1 x.2++
      readFamilyCircuitLayers (bodySelectorQuantumDescription Q x.1 x.2)) :=
    Poly.comp (f := fun x : List (List Str) × List (List Str) => x.1++x.2)
      (g := fun x : Str × List (Str × Str) => (bodyDWordLayers Q x.1 x.2,
        readFamilyCircuitLayers (bodySelectorQuantumDescription Q x.1 x.2)))
      Poly.list_append (Poly.pair hd hs)
  have h := Poly.comp (f := fun x : List (List Str) × List (List Str) => x.1++x.2)
    (g := fun x : Str × List (Str × Str) =>
      (readFamilyCircuitLayers (bodyPreparedQuantumDescription Q x.1 x.2),
        bodyDWordLayers Q x.1 x.2++
          readFamilyCircuitLayers (bodySelectorQuantumDescription Q x.1 x.2)))
    Poly.list_append (Poly.pair hp htail)
  simpa only [bodyQuantumWordLayers,List.append_assoc] using h

theorem bodyQuantumWordLayers_correct (Q : QueryProgram) (D : Family) (n : ℕ) :
    bodyQuantumWordLayers Q (unary n) (describedQueryBlocks D (Q.padding.eval n))=
      (bodyCircuit Q D n).map (List.map encInstr) := by
  unfold bodyQuantumWordLayers
  rw [bodyPreparedQuantumDescription_correct,readFamilyCircuitLayers_correct,
    bodyDWordLayers_correct,bodySelectorQuantumDescription_correct,readFamilyCircuitLayers_correct]
  simp only [bodyPreparedBooleanFamily,bodySelectorBooleanFamily,BooleanFamily.reversible,ReversibleFamily.compile,
    bodyCircuit,List.map_append]

@[fun_prop] theorem bodyDescription_poly (Q : QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => bodyDescription Q x.1 x.2) := by
  unfold bodyDescription
  fun_prop

/-- The real native final emitter outputs the exact platform Family description. -/
theorem bodyDescription_correct (Q : QueryProgram) (D : Family) (n : ℕ) :
    bodyDescription Q (unary n) (describedQueryBlocks D (Q.padding.eval n))=
      encFamilyAt (bodyFamily Q D) n := by
  unfold bodyDescription
  rw [lengthToken_eq,bodyOutputWord_correct,bodyQuantumWordLayers_correct]
  simp only [serializeWords_eq,List.map_map,Function.comp_def]
  rfl

/-- The complete coherent body is generated using the original Uniform D
machine, with real stock subroutine calls and the proved native final emitter. -/
theorem bodyFamily_uniform (Q : QueryProgram) (D : Family) (hD : Uniform D) :
    Uniform (bodyFamily Q D) := by
  let builder : Str × List (Str × Str) → Str := fun x => bodyDescription Q x.1 x.2
  let generator : Str → Str := fun word => builder (word,describedQueryBlocks D (Q.padding.eval word.length))
  have hg : PolyTimeComputable generator := uniformDTable_builder_polyTime D hD Q.padding builder
    (bodyDescription_poly Q)
  refine ⟨generator,hg,?_⟩
  intro n
  change bodyDescription Q (unary n)
    (describedQueryBlocks D (Q.padding.eval (unary n).length))=_
  rw [show (unary n).length=n by simp [unary]]
  exact bodyDescription_correct Q D n

/-- A full actual IsQPT certificate for the coherent preprocessing/D/selector body. -/
theorem bodyFamily_isQPT (Q : QueryProgram) (D : Family) (hD : IsQPT D) :
    IsQPT (bodyFamily Q D) :=
  ⟨bodyFamily_uniform Q D hD.1,
    bodyFamily_wellFormed Q D hD.2.1,
    bodyFamily_polyBounded Q D hD.2.2⟩

end Integration9_9.GenericBody

end

end P2MDyadicModule80

/- Helper module Solutions.AdvantageBridgeGenericBodyPointerSemantics. -/
section P2MDyadicModule81

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBody

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary

open Integration9_9.LARCoinLayout

/-- Exact actual flag-register semantics, under only the mathematical encoding
identity for the actual query-output machine. -/
theorem bodyFlagPointer_value (Q : QueryProgram) (query : Str → Str)
    (hquery : ∀ word, Q.f word = encodeQueryOutput
      (List.replicate (Q.padding.eval word.length) ()) (query word))
    (word : Str) (index : ℕ) (hi : index ≤ Q.padding.eval word.length) :
    generatedQueryBits (bodyQueryProgram Q) word
      ((bodyFlagAddresses Q (unary word.length))[index]'(by
        simp only [bodyFlagAddresses_length,unary,List.length_replicate]; omega)) =
      decide ((query word).length = index) := by
  let P := bodyQueryProgram Q
  have hcap := bodyQueryOutput_capacity Q word.length
  let cell : Fin (capacity P word.length) := ⟨index,by dsimp only [P]; omega⟩
  have haddr : (bodyFlagAddresses Q (unary word.length))[index]'(by
      simp only [bodyFlagAddresses_length,unary,List.length_replicate]; omega) =
      generatedProgramOutputAddress P (unary word.length) cell.val := by
    unfold bodyFlagAddresses
    rw [generatedAddressRange_get_any _ _ _ 0 index (by
      simp only [List.length_append,List.length_singleton,queryWireSlots_length,unary,List.length_replicate]; omega)]
    simp only [zero_add,P,cell]
  rw [haddr,generatedQueryBits_output]
  change decide (some true = (Q.f word)[index]?) = _
  rw [hquery word]
  rw [encodeQueryOutput_flag _ _ index (by simpa only [List.length_replicate] using hi)]
  by_cases he : (query word).length = index <;> simp [he]

/-- Every real payload pointer reads the corresponding true query bit, with
false beyond its end. The premise is an equality of output strings. -/
theorem bodyPayloadPointer_value (Q : QueryProgram) (query : Str → Str)
    (hquery : ∀ word, Q.f word = encodeQueryOutput
      (List.replicate (Q.padding.eval word.length) ()) (query word))
    (word : Str) (index : ℕ) (hi : index < Q.padding.eval word.length) :
    generatedQueryBits (bodyQueryProgram Q) word
      ((bodyPayloadAddresses Q (unary word.length))[index]'(by
        simpa only [bodyPayloadAddresses_length,unary,List.length_replicate] using hi)) =
      ((query word)[index]?).getD false := by
  let P := bodyQueryProgram Q
  have hcap := bodyQueryOutput_capacity Q word.length
  let cell : Fin (capacity P word.length) := ⟨Q.padding.eval word.length + 1 + index,by dsimp only [P]; omega⟩
  have haddr : (bodyPayloadAddresses Q (unary word.length))[index]'(by
      simpa only [bodyPayloadAddresses_length,unary,List.length_replicate] using hi) =
      generatedProgramOutputAddress P (unary word.length) cell.val := by
    unfold bodyPayloadAddresses
    rw [generatedAddressRange_get_any _ _ _ _ index (by
      simpa only [queryWireSlots_length,unary,List.length_replicate] using hi)]
    simp only [queryWireSlots_length,unary,List.length_replicate,cell,P]
  rw [haddr,generatedQueryBits_output]
  change decide (some true = (Q.f word)[Q.padding.eval word.length + 1 + index]?) = _
  have hbit := encodeQueryOutput_bit (List.replicate (Q.padding.eval word.length) ()) (query word) index
    (by simpa only [List.length_replicate] using hi)
  simp only [List.length_replicate] at hbit
  rw [hquery word,hbit]
  cases hb : ((query word)[index]?).getD false <;> simp [hb]

end Integration9_9.GenericBody

end

end P2MDyadicModule81

/- Helper module Solutions.AdvantageBridgeBundleBasis. -/
section P2MDyadicModule82

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

theorem familyBlock_input_basis (D : Family) (query : Str) (length : ℕ) :
    (familyBlock D length (fun index => (query[index.val]?).getD false)).input=
      computationalBasis (familyInputBits D query length) := by
  change basisInput (a := D.anc length) (fun index => (query[index.val]?).getD false)=_
  rw [basisInput_eq_computationalBasis]
  apply congrArg computationalBasis
  funext index
  refine Fin.addCases (fun i => ?_) (fun i => ?_) index
  · simp [familyInputBits,i.isLt]
  · simp (disch := omega) [familyInputBits]

theorem indexedQueryBundleState_basis (D : Family) (query : Str) (lengths : List ℕ) :
    bundleState (indexedQueryBlocks D query lengths)=
      computationalBasis (fun index => bundleNaturalBits D query lengths index.val) := by
  induction lengths with
  | nil =>
    change (fun _ : Bits 0 => (1 : ℂ))=computationalBasis (fun _ : Fin 0 => false)
    funext output
    have he : output=(fun _ : Fin 0 => false) := Subsingleton.elim _ _
    simp only [computationalBasis,if_pos he]
  | cons length rest ih =>
    change tensorState (familyBlock D length (fun index => (query[index.val]?).getD false)).input
      (bundleState (indexedQueryBlocks D query rest))=_
    rw [familyBlock_input_basis,ih,←computationalBasis_tensor]
    apply congrArg computationalBasis
    funext index
    refine Fin.addCases (fun i => ?_) (fun i => ?_) index
    · have hi : i.val<length+(D.anc length+1) := i.isLt
      simp [bundleNaturalBits,familyInputBits,hi]
    · simp (disch := omega) [bundleNaturalBits,familyBlock]

theorem queryBlocks_eq_indexed (D : Family) (maximum : ℕ) (query : Str) :
    queryBlocks D maximum query=indexedQueryBlocks D query (List.range (maximum+1)) := by
  have hmap {α : Type} (f : ℕ → α) :
      List.ofFn (fun index : Fin (maximum+1) => f index.val)=(List.range (maximum+1)).map f := by
    apply List.ext_getElem
    · simp
    · intro index hi hj
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  exact hmap (fun length => familyBlock D length (fun index => (query[index.val]?).getD false))

theorem queryBundleState_basis (D : Family) (maximum : ℕ) (query : Str) :
    bundleState (queryBlocks D maximum query)=
      computationalBasis (fun index => bundleNaturalBits D query (List.range (maximum+1)) index.val) := by
  have h := indexedQueryBundleState_basis D query (List.range (maximum+1))
  rw [←queryBlocks_eq_indexed D maximum query] at h
  exact h

theorem sourceValueAt_get (sources : List (Bool × ℕ)) (state : ℕ → Bool) (index : ℕ)
    (hi : index < sources.length) :
    sourceValueAt sources state index=registerLoadValue sources[index] state := by
  simp only [sourceValueAt,List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some]

theorem sourceValueAt_append (first second : List (Bool × ℕ)) (state : ℕ → Bool) (index : ℕ) :
    sourceValueAt (first++second) state index=
      if index < first.length then sourceValueAt first state index else sourceValueAt second state (index-first.length) := by
  unfold sourceValueAt
  by_cases hi : index < first.length
  · rw [List.getElem?_append_left hi,if_pos hi]
  · rw [List.getElem?_append_right (by omega),if_neg hi]

theorem dBlockLoad_valueAt (querySources : List ℕ) (request slots : List Unit) (state : ℕ → Bool) (index : ℕ) :
    sourceValueAt (dBlockLoadSources querySources request slots) state index=
      if index < slots.length then
        (if index < request.length then state ((querySources[index]?).getD 0) else false)
      else false := by
  unfold sourceValueAt dBlockLoadSources
  by_cases hi : index < slots.length
  · rw [List.getElem?_map,List.getElem?_range hi]
    simp only [Option.map_some,Option.getD_some,registerLoadValue,decide_eq_true_eq,if_pos hi]
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp [hi]

theorem describedQueryBlocks_eq_lengths (D : Family) (maximum : ℕ) :
    describedQueryBlocks D maximum=lengthDescriptions D (List.range (maximum+1)) := by
  apply List.ext_getElem
  · simp [describedQueryBlocks,lengthDescriptions]
  · intro index hi hj
    simp only [describedQueryBlocks,lengthDescriptions,List.getElem_map,List.getElem_range,List.getElem_ofFn]

/-- Every actual copied D bit is the correct query bit; the whole concatenated
load is proved directly, including all ancilla/output zero positions. -/
theorem dBundleLoad_valueAt (D : Family) (query : Str) (lengths : List ℕ)
    (querySources : List ℕ) (state : ℕ → Bool)
    (hq : ∀ length∈lengths,∀ index < length,state ((querySources[index]?).getD 0)=(query[index]?).getD false)
    (index : ℕ) :
    sourceValueAt (dBundleLoadSources querySources (lengthDescriptions D lengths)) state index=
      bundleNaturalBits D query lengths index := by
  induction lengths generalizing index with
  | nil => rfl
  | cons length rest ih =>
    unfold lengthDescriptions dBundleLoadSources
    simp only [List.map_cons,List.flatMap_cons,readFamilyFrame_correct]
    simp only [unary,List.map_replicate]
    rw [sourceValueAt_append,dBlockLoadSources_length]
    simp only [List.length_replicate]
    by_cases hi : index < length+(D.anc length+1)
    · rw [if_pos hi,dBlockLoad_valueAt]
      simp only [List.length_replicate,if_pos hi,bundleNaturalBits]
      by_cases hj : index < length
      · rw [if_pos hj,if_pos hj,hq length (by simp) index hj]
      · rw [if_neg hj,if_neg hj]
    · rw [if_neg hi]
      change sourceValueAt (dBundleLoadSources querySources (lengthDescriptions D rest)) state
        (index-(length+(D.anc length+1)))=_
      rw [ih (fun other ho => hq other (by simp [ho]))]
      simp only [bundleNaturalBits,if_neg hi]

end InfoLossLAR.WorstCase

end P2MDyadicModule82

/- Helper module Solutions.AdvantageBridgeBodyPreparedState. -/
section P2MDyadicModule83

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

theorem castBodyState_basis {left right : ℕ} (h : left=right) (bits : Bits left) :
    castBodyState h (computationalBasis bits)=
      computationalBasis (fun index => bits (Fin.cast h.symm index)) := by
  cases h
  rfl

theorem runLayered_castBody {left right : ℕ} (h : left=right)
    (circuit : Layered left) (state : QState left) :
    runLayered (castBodyCircuit h circuit) (castBodyState h state)=
      castBodyState h (runLayered circuit state) := by
  cases h
  rfl

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule83

/- Helper module Solutions.AdvantageBridgeBodyDState. -/
section P2MDyadicModule84

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

/-- Sequential literal layered circuits compose by actual platform semantics. -/
theorem runLayered_append_actual {width : ℕ} (first second : Layered width) (state : QState width) :
    runLayered (first++second) state=runLayered second (runLayered first state) := List.foldl_append

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule84

/- Helper module Solutions.AdvantageBridgeSelectorTensor. -/
section P2MDyadicModule85

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

/-- A basis ancilla can be summed out exactly even for an arbitrary event. -/
theorem tensorBasis_event_probability {left right : ℕ} (state : QState left)
    (bits : Bits right) (event : Bits (left+right) → Bool) :
    (∑ input : Bits (left+right),if event input then
      ‖tensorState state (computationalBasis bits) input‖^2 else 0)=
      ∑ input : Bits left,if event (Fin.append input bits) then ‖state input‖^2 else 0 := by
  classical
  have hsplit (input : Bits (left+right)) :
      Fin.append (leftRegister input) (rightRegister input)=input := by
    funext index
    refine Fin.addCases (fun i => ?_) (fun i => ?_) index
    · simp only [Fin.append_left,leftRegister]
    · simp only [Fin.append_right,rightRegister]
  have hsum := sum_registers (fun first : Bits left => fun second : Bits right =>
    if event (Fin.append first second) then ‖state first*computationalBasis bits second‖^2 else 0)
  simp only [hsplit] at hsum
  change (∑ input : Bits (left+right),if event input then
    ‖state (leftRegister input)*computationalBasis bits (rightRegister input)‖^2 else 0)=_
  rw [hsum]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.sum_eq_single bits]
  · simp [computationalBasis]
  · intro second _ hne
    simp [computationalBasis,hne]
  · simp

/-- A zero-padded finite register has the same values at every old address. -/
theorem selectorBitsExtension_append_prefix {left right : ℕ} (first : Bits left) (second : Bits right)
    (index : ℕ) (hi : index < left) :
    selectorBitsExtension (Fin.append first second) index=selectorBitsExtension first index := by
  have htotal : index < left+right := by omega
  change (if h : index < left+right then _ else false)=_
  rw [dif_pos htotal]
  have hindex : (⟨index,htotal⟩ : Fin (left+right))=Fin.castAdd right ⟨index,hi⟩ := rfl
  rw [hindex,Fin.append_left]
  simp [selectorBitsExtension,hi]

/-- The concrete selector circuit consumes arbitrary amplitudes on its control
register and fresh zero workspace, with exactly the stated selected event. -/
theorem multiSelector_tensor_probability {start left : ℕ} (choices : List (ℕ × ℕ))
    (hl : left < start) (hc : ∀ choice∈choices,choice.1 < start ∧ choice.2 < start)
    (state : QState start) :
    (∑ output : Bits (start+(4*choices.length+1)),if output
        ⟨multiSelectorOutput start left choices,by
          have := multiSelectorOutput_lt start left choices hl; omega⟩ then
      ‖runLayered (compileReversible (booleanToReversible
        (BooleanProgram.gates start (multiSelectorOps start left choices)
          (by rw [multiSelectorOps_length]; omega))))
        (tensorState state (computationalBasis (fun _ => false))) output‖^2 else 0)=
      ∑ input : Bits start,if multiSelectorValue (selectorBitsExtension input)
        (selectorBitsExtension input left) choices then ‖state input‖^2 else 0 := by
  classical
  rw [multiSelector_probability choices hl hc (by omega)]
  · rw [tensorBasis_event_probability]
    apply Finset.sum_congr rfl
    intro input _
    rw [selectorBitsExtension_append_prefix input _ left hl]
    rw [multiSelectorValue_congr choices _ (selectorBitsExtension input) _ (fun choice hm => by
      have h := hc choice hm
      exact ⟨selectorBitsExtension_append_prefix input _ choice.1 h.1,
        selectorBitsExtension_append_prefix input _ choice.2 h.2⟩)]
  · intro input hi index hlow hhigh
    have hright : rightRegister input=(fun _ : Fin (4*choices.length+1) => false) := by
      by_contra hn
      apply hi
      simp [tensorState,computationalBasis,hn]
    have hindex : index < start+(4*choices.length+1) := by omega
    have hoffset : index-start < 4*choices.length+1 := by omega
    change (if h : index < start+(4*choices.length+1) then input ⟨index,h⟩ else false)=false
    rw [dif_pos hindex]
    have heq : (⟨index,hindex⟩ : Fin (start+(4*choices.length+1)))=
        Fin.natAdd start ⟨index-start,hoffset⟩ := by apply Fin.ext; simp; omega
    rw [heq]
    exact congrFun hright ⟨index-start,hoffset⟩

end InfoLossLAR.WorstCase

end P2MDyadicModule85

/- Helper module Solutions.AdvantageBridgeBodyAcceptance. -/
section P2MDyadicModule86

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

/-- A retained computational-basis prefix has no probabilistic contribution. -/
theorem basisTensor_event_probability {left right : ℕ} (bits : Bits left)
    (state : QState right) (event : Bits (left+right) → Bool) :
    (∑ input : Bits (left+right),if event input then
      ‖tensorState (computationalBasis bits) state input‖^2 else 0)=
      ∑ input : Bits right,if event (Fin.append bits input) then ‖state input‖^2 else 0 := by
  classical
  have hsplit (input : Bits (left+right)) :
      Fin.append (leftRegister input) (rightRegister input)=input := by
    funext index
    refine Fin.addCases (fun i => ?_) (fun i => ?_) index
    · simp only [Fin.append_left,leftRegister]
    · simp only [Fin.append_right,rightRegister]
  have hsum := sum_registers (fun first : Bits left => fun second : Bits right =>
    if event (Fin.append first second) then ‖computationalBasis bits first*state second‖^2 else 0)
  simp only [hsplit] at hsum
  change (∑ input : Bits (left+right),if event input then
    ‖computationalBasis bits (leftRegister input)*state (rightRegister input)‖^2 else 0)=_
  rw [hsum,Finset.sum_eq_single bits]
  · simp [computationalBasis]
  · intro first _ hne
    simp [computationalBasis,hne]
  · simp

end InfoLossLAR.WorstCase

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial QMCNumericRuntime TM2PlatformSerialization

open scoped BigOperators

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule86

/- Helper module Solutions.AdvantageBridgeBodyProbability. -/
section P2MDyadicModule87

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity QMCNumericRuntime Integration9_9.TM2PlatformSerialization

private theorem output_list_get_eq {α : Type} {length : ℕ} (items : List α)
    (f : Fin length → α) (h : items=List.ofFn f) (index : ℕ)
    (hi : index < items.length) (hn : index < length) : items[index]=f ⟨index,hn⟩ := by
  subst items
  simp only [List.getElem_ofFn]

private theorem emittedOutput_get (D : Family) (maximum : ℕ) (query : Str)
    (index : ℕ) (hi : index ≤ maximum)
    (hit : index < (emitDOutputs (describedQueryBlocks D maximum)).length) :
    (emitDOutputs (describedQueryBlocks D maximum))[index]=
      encNat (bundleOutput (queryBlocks D maximum query)
        ⟨index,by simp only [queryBlocks,List.length_ofFn]; omega⟩).val :=
  output_list_get_eq _ _ (emitDOutputs_correct D maximum query) index hit _

/-- The actual physical candidate output index is independent of query bits. -/
theorem queryBlocks_output_val_independent (D : Family) (maximum : ℕ) (first second : Str)
    (index : ℕ) (hi : index ≤ maximum) :
    (bundleOutput (queryBlocks D maximum first) ⟨index,by simp only [queryBlocks,List.length_ofFn]; omega⟩).val=
      (bundleOutput (queryBlocks D maximum second) ⟨index,by simp only [queryBlocks,List.length_ofFn]; omega⟩).val := by
  have hit : index < (emitDOutputs (describedQueryBlocks D maximum)).length := by
    rw [emitDOutputs_correct D maximum first]
    simpa only [List.length_ofFn,queryBlocks] using (show index < maximum+1 by omega)
  have h := (emittedOutput_get D maximum first index hi hit).symm.trans
    (emittedOutput_get D maximum second index hi hit)
  have hd := congrArg inputWidth h
  have hn (number : ℕ) : inputWidth (encNat number)=number := by
    rw [←unaryPayload_length,unaryPayload_number]
    simp only [unary,List.length_replicate]
  simpa only [hn] using hd

end InfoLossLAR.WorstCase

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open scoped BigOperators

/-- A pure physical-width cast preserves the probability of any selected wire. -/
theorem castBodyState_output_probability {left right : ℕ} (h : left=right)
    (state : QState left) (output : Fin left) :
    (∑ input : Bits right,if input (Fin.cast h output) then ‖castBodyState h state input‖^2 else 0)=
      ∑ input : Bits left,if input output then ‖state input‖^2 else 0 := by
  cases h
  rfl

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule87

/- Helper module Solutions.AdvantageBridgeGenericBodySpec. -/
section P2MDyadicModule88

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBodySemantics

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open Integration9_9.GenericBody Integration9_9.LARCoinLayout

theorem bodyFlagPointer_value (R : QuerySpecification) (word : Str)
    (index : ℕ) (hi : index ≤ R.machine.padding.eval word.length) :
    generatedQueryBits (GenericBody.bodyQueryProgram R.machine) word
      ((GenericBody.bodyFlagAddresses R.machine (unary word.length))[index]'(by
        simp only [GenericBody.bodyFlagAddresses_length,unary,List.length_replicate]; omega))=
      decide ((R.query word).length=index) :=
  GenericBody.bodyFlagPointer_value R.machine R.query R.encoding word index hi

theorem bodyPayloadPointer_value (R : QuerySpecification) (word : Str)
    (index : ℕ) (hi : index < R.machine.padding.eval word.length) :
    generatedQueryBits (GenericBody.bodyQueryProgram R.machine) word
      ((GenericBody.bodyPayloadAddresses R.machine (unary word.length))[index]'(by
        simpa only [GenericBody.bodyPayloadAddresses_length,unary,List.length_replicate] using hi))=
      ((R.query word)[index]?).getD false :=
  GenericBody.bodyPayloadPointer_value R.machine R.query R.encoding word index hi

end Integration9_9.GenericBodySemantics

end

end P2MDyadicModule88

/- Helper module Solutions.AdvantageBridgeGenericQueryFactory. -/
section P2MDyadicModule89

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBodySemantics

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.GenericBody Integration9_9.LARCoinLayout

theorem specificationOfPre_query {pre : Str → Str} (P : PolyProgram id id pre) (coins : Polynomial ℕ)
    (tape word : Str) (ht : tape.length=coins.eval word.length) :
    (specificationOfPre P coins).query (tape++word)=pre (encPair tape word) := by
  change pre (coinFirstPair coins (tape++word))=_
  rw [coinFirstPair_eq coins tape word ht]

end Integration9_9.GenericBodySemantics

end

end P2MDyadicModule89

/- Helper module Solutions.AdvantageBridgeGenericBodyPreparedState. -/
section P2MDyadicModule90

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBodySemantics

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open Integration9_9.GenericBody

/-- The actual whole D-load list, evaluated at the compiled query result. -/
theorem bodyDLoad_valueAt (R : QuerySpecification) (D : Family)
    (word : Str) (index : ℕ) :
    sourceValueAt (bodySources R.machine D word.length)
      (generatedQueryBits (bodyQueryProgram R.machine) word) index=
      bundleNaturalBits D (R.query word) (List.range (R.machine.padding.eval word.length+1)) index := by
  unfold bodySources
  rw [describedQueryBlocks_eq_lengths]
  apply dBundleLoad_valueAt
  intro length hl j hj
  have hlen : length ≤ R.machine.padding.eval word.length := by
    have := List.mem_range.mp hl
    omega
  have hjp : j < R.machine.padding.eval word.length := by omega
  have hjs : j < (bodyPayloadAddresses R.machine (unary word.length)).length := by
    simpa only [bodyPayloadAddresses_length,unary,List.length_replicate] using hjp
  rw [List.getElem?_eq_getElem hjs,Option.getD_some]
  exact bodyPayloadPointer_value R word j hjp

theorem bodyPreparedBits_prefix (R : QuerySpecification) (D : Family)
    (word : Str) (index : ℕ) (hi : index < bodyPreWidth R.machine word.length) :
    bodyPreparedBits R D word index=
      generatedQueryBits (bodyQueryProgram R.machine) word index :=
  preparedLoadOps_prefix _ _ _ _ hi

theorem bodyPreparedBits_D (R : QuerySpecification) (D : Family)
    (word : Str) (index : ℕ) (hi : index < bodyDWidth R.machine D word.length) :
    bodyPreparedBits R D word
      (bodyPreWidth R.machine word.length+index)=
      bundleNaturalBits D (R.query word) (List.range (R.machine.padding.eval word.length+1)) index := by
  have his : index < (bodySources R.machine D word.length).length := by
    simpa only [bodySources_length] using hi
  unfold bodyPreparedBits bodyPreWidth
  rw [preparedLoadOps_written (bodyQueryProgram R.machine) word
    (bodySources R.machine D word.length)
    (bodyDLoadSources_valid R.machine D word.length) index his]
  rw [←sourceValueAt_get _ _ index his,bodyDLoad_valueAt]

theorem bodyPreparedBits_after (R : QuerySpecification) (D : Family)
    (word : Str) (index : ℕ)
    (hi : bodyPreWidth R.machine word.length+bodyDWidth R.machine D word.length ≤ index) :
    bodyPreparedBits R D word index=false := by
  unfold bodyPreparedBits
  rw [BooleanProgram.run_after]
  · exact wordExtension_after word index (by unfold bodyPreWidth at hi; omega)
  · rw [preparedLoadOps_length,bodySources_length]
    unfold bodyPreWidth at hi
    omega

/-- The actual first phase, on the platform's true zero ancillary input. -/
theorem bodyPreparedCircuit_basis (R : QuerySpecification) (D : Family)
    (word : Str) :
    runLayered (compileReversible (booleanToReversible (bodyPreparedGates R.machine D word.length)))
      (basisInput (a := bodyAnc R.machine D word.length) (toBits word))=
      computationalBasis (fun index => bodyPreparedBits R D word index.val) := by
  rw [basisInput_eq_computationalBasis,wordExtension_basis]
  unfold bodyPreparedGates bodyPreparedBits computationalBasis
  exact BooleanProgram.circuit_basis _ _ (bodyPrepared_valid R.machine D word.length)
    (wordExtension word) (fun index hi _ => wordExtension_after word index hi)

theorem castBodyState_basis {left right : ℕ} (h : left=right) (bits : Bits left) :
    castBodyState h (computationalBasis bits)=
      computationalBasis (fun index => bits (Fin.cast h.symm index)) := by
  cases h
  rfl

theorem runLayered_castBody {left right : ℕ} (h : left=right)
    (circuit : Layered left) (state : QState left) :
    runLayered (castBodyCircuit h circuit) (castBodyState h state)=
      castBodyState h (runLayered circuit state) := by
  cases h
  rfl

/-- The true query-content tensor has exactly the already emitted body width. -/
theorem bodyPreparedTensor_width (R : QuerySpecification) (D : Family)
    (word : Str) :
    (bodyPreWidth R.machine word.length+
      bundleWidth (queryBlocks D (R.machine.padding.eval word.length) (R.query word)))+
      (4*(R.machine.padding.eval word.length+1)+1)=bodyWidth R.machine D word.length := by
  rw [queryBlocks_width_independent D _ (R.query word) [],bodyWidth_formula]
  rfl

/-- Exact tensor separation of the prepared query computation, all candidate D
inputs, and fresh selector scratch. No measurement or disposal is performed. -/
theorem bodyPreparedState_tensor (R : QuerySpecification) (D : Family)
    (word : Str) :
    computationalBasis (fun index : Fin (bodyWidth R.machine D word.length) =>
      bodyPreparedBits R D word index.val)=
      castBodyState (bodyPreparedTensor_width R D word)
        (tensorState
          (tensorState (computationalBasis (result (bodyQueryProgram R.machine) word))
            (bundleState (queryBlocks D (R.machine.padding.eval word.length) (R.query word))))
          (computationalBasis (fun _ => false))) := by
  rw [queryBundleState_basis,←computationalBasis_tensor,←computationalBasis_tensor,castBodyState_basis]
  apply congrArg computationalBasis
  have hwidth := queryBlocks_width_independent D (R.machine.padding.eval word.length)
    (R.query word) []
  have hbits (index : Fin ((bodyPreWidth R.machine word.length+
      bundleWidth (queryBlocks D (R.machine.padding.eval word.length) (R.query word)))+
      (4*(R.machine.padding.eval word.length+1)+1))) :
      bodyPreparedBits R D word index.val=
        (Fin.append (Fin.append (result (bodyQueryProgram R.machine) word)
          (fun index => bundleNaturalBits D (R.query word)
            (List.range (R.machine.padding.eval word.length+1)) index.val)) (fun _ => false)) index := by
    refine Fin.addCases (fun block => ?_) (fun scratch => ?_) index
    · refine Fin.addCases (fun previous => ?_) (fun data => ?_) block
      · simp only [Fin.val_castAdd,Fin.append_left]
        rw [bodyPreparedBits_prefix R D word previous.val previous.isLt]
        exact selectorBitsExtension_get _ previous
      · simp only [Fin.val_castAdd,Fin.val_natAdd,Fin.append_left]
        dsimp only [bodyPreWidth] at *
        rw [Fin.append_right]
        change bodyPreparedBits R D word
          (bodyPreWidth R.machine word.length+data.val)=
          bundleNaturalBits D (R.query word)
            (List.range (R.machine.padding.eval word.length+1)) data.val
        exact bodyPreparedBits_D R D word data.val (by
          change data.val < bundleWidth (queryBlocks D (R.machine.padding.eval word.length) [])
          rw [←hwidth]
          exact data.isLt)
    · simp only [Fin.val_natAdd]
      dsimp only [bodyPreWidth] at *
      rw [Fin.append_right]
      change bodyPreparedBits R D word
        (bodyPreWidth R.machine word.length+
          bundleWidth (queryBlocks D (R.machine.padding.eval word.length) (R.query word))+scratch.val)=false
      apply bodyPreparedBits_after
      change bodyPreWidth R.machine word.length+
        bundleWidth (queryBlocks D (R.machine.padding.eval word.length) []) ≤ _
      rw [←hwidth]
      omega
  funext index
  simpa only [Fin.val_cast] using hbits (Fin.cast (bodyPreparedTensor_width R D word).symm index)

end Integration9_9.GenericBodySemantics

end

end P2MDyadicModule90

/- Helper module Solutions.AdvantageBridgeGenericBodyDState. -/
section P2MDyadicModule91

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBodySemantics

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open Integration9_9.GenericBody

/-- Transporting equal physical circuits to the same register preserves their
literal layered gate descriptions. -/
theorem packedCircuit_cast {left right total : ℕ} (first : Layered left) (second : Layered right)
    (h : (⟨left,first⟩ : Σ width : ℕ,Layered width)=⟨right,second⟩)
    (hf : left=total) (hs : right=total) :
    castBodyCircuit hf first=castBodyCircuit hs second := by
  cases h
  rfl

/-- The emitted D circuit was generated without seeing the query. It is exactly
the circuit on the true query-input tensor, including every wire offset. -/
theorem bodyDCircuit_query (R : QuerySpecification) (D : Family)
    (word : Str) :
    bodyDCircuit R.machine D word.length=
      castBodyCircuit (bodyPreparedTensor_width R D word)
        (leftCircuit (m := 4*(R.machine.padding.eval word.length+1)+1)
          (rightCircuit (n := bodyPreWidth R.machine word.length)
            (bundleCircuit (queryBlocks D (R.machine.padding.eval word.length) (R.query word))))) := by
  have h := congrArg (fun circuit : (Σ width : ℕ,Layered width) =>
      (⟨(bodyPreWidth R.machine word.length+circuit.1)+(4*(R.machine.padding.eval word.length+1)+1),
        leftCircuit (m := 4*(R.machine.padding.eval word.length+1)+1)
          (rightCircuit (n := bodyPreWidth R.machine word.length) circuit.2)⟩ :
        Σ width : ℕ,Layered width))
    (queryBlocks_physical_independent D (R.machine.padding.eval word.length) [] (R.query word))
  unfold bodyDCircuit
  exact packedCircuit_cast _ _ h _ _

/-- Exact coherent state after all actual D circuits: the query compiler's
retained output, the genuine tensor of D output states, and zero selector scratch. -/
theorem bodyDState_tensor (R : QuerySpecification) (D : Family)
    (word : Str) :
    runLayered (bodyDCircuit R.machine D word.length)
      (computationalBasis (fun index : Fin (bodyWidth R.machine D word.length) =>
        bodyPreparedBits R D word index.val))=
      castBodyState (bodyPreparedTensor_width R D word)
        (tensorState
          (tensorState (computationalBasis (result (bodyQueryProgram R.machine) word))
            (runLayered (bundleCircuit (queryBlocks D (R.machine.padding.eval word.length) (R.query word)))
              (bundleState (queryBlocks D (R.machine.padding.eval word.length) (R.query word)))))
          (computationalBasis (fun _ => false))) := by
  rw [bodyPreparedState_tensor,bodyDCircuit_query,runLayered_castBody,leftCircuit_tensor,rightCircuit_tensor]

/-- Sequential literal layered circuits compose by actual platform semantics. -/
theorem runLayered_append_actual {width : ℕ} (first second : Layered width) (state : QState width) :
    runLayered (first++second) state=runLayered second (runLayered first state) := List.foldl_append

/-- The exact first two phases of the single emitted body, before selecting its
measured output bit. -/
theorem bodyFirstPhases_tensor (R : QuerySpecification) (D : Family)
    (word : Str) :
    runLayered
      (compileReversible (booleanToReversible (bodyPreparedGates R.machine D word.length))++
        bodyDCircuit R.machine D word.length)
      (basisInput (a := bodyAnc R.machine D word.length) (toBits word))=
      castBodyState (bodyPreparedTensor_width R D word)
        (tensorState
          (tensorState (computationalBasis (result (bodyQueryProgram R.machine) word))
            (runLayered (bundleCircuit (queryBlocks D (R.machine.padding.eval word.length) (R.query word)))
              (bundleState (queryBlocks D (R.machine.padding.eval word.length) (R.query word)))))
          (computationalBasis (fun _ => false))) := by
  rw [runLayered_append_actual,bodyPreparedCircuit_basis,bodyDState_tensor]

end Integration9_9.GenericBodySemantics

end

end P2MDyadicModule91

/- Helper module Solutions.AdvantageBridgeGenericBodySelection. -/
section P2MDyadicModule92

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBodySemantics

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open Integration9_9.GenericBody

open scoped BigOperators

/-- A middle-register dimension transport is exactly the full tensor transport. -/
theorem castBodyState_tensor_middle {left first second right total : ℕ}
    (h : first=second) (hfirst : (left+first)+right=total)
    (hsecond : (left+second)+right=total)
    (prefixState : QState left) (middleState : QState first) (suffixState : QState right) :
    castBodyState hfirst (tensorState (tensorState prefixState middleState) suffixState)=
      castBodyState hsecond (tensorState (tensorState prefixState (castBodyState h middleState)) suffixState) := by
  cases h
  rfl

/-- Selector probability is unchanged by a pure physical-width equality cast. -/
theorem multiSelector_cast_tensor_probability {start left total : ℕ} (choices : List (ℕ × ℕ))
    (hl : left < start) (hc : ∀ choice∈choices,choice.1 < start ∧ choice.2 < start)
    (h : start+(4*choices.length+1)=total) (state : QState start) :
    (∑ output : Bits total,if output
        ⟨multiSelectorOutput start left choices,by
          have := multiSelectorOutput_lt start left choices hl; omega⟩ then
      ‖runLayered (compileReversible (booleanToReversible
        (BooleanProgram.gates start (multiSelectorOps start left choices)
          (by rw [multiSelectorOps_length]; omega))))
        (castBodyState h (tensorState state (computationalBasis (fun _ => false)))) output‖^2 else 0)=
      ∑ input : Bits start,if multiSelectorValue (selectorBitsExtension input)
        (selectorBitsExtension input left) choices then ‖state input‖^2 else 0 := by
  cases h
  exact multiSelector_tensor_probability choices hl hc state

/-- The same exact selector statement with an explicitly equal scratch budget. -/
theorem multiSelector_cast_tensor_probability_scratch {start left total scratch : ℕ}
    (choices : List (ℕ × ℕ)) (hl : left < start)
    (hc : ∀ choice∈choices,choice.1 < start ∧ choice.2 < start)
    (hsize : scratch=4*choices.length+1) (h : start+scratch=total) (state : QState start) :
    (∑ output : Bits total,if output
        ⟨multiSelectorOutput start left choices,by
          have := multiSelectorOutput_lt start left choices hl; omega⟩ then
      ‖runLayered (compileReversible (booleanToReversible
        (BooleanProgram.gates start (multiSelectorOps start left choices)
          (by rw [multiSelectorOps_length]; omega))))
        (castBodyState h (tensorState state (computationalBasis (fun _ => false)))) output‖^2 else 0)=
      ∑ input : Bits start,if multiSelectorValue (selectorBitsExtension input)
        (selectorBitsExtension input left) choices then ‖state input‖^2 else 0 := by
  subst scratch
  exact multiSelector_cast_tensor_probability choices hl hc h state

/-- The full emitted body state before the selector, expressed on its actual
static physical D register. -/
theorem bodyFirstPhases_static (R : QuerySpecification) (D : Family)
    (word : Str) :
    runLayered
      (compileReversible (booleanToReversible (bodyPreparedGates R.machine D word.length))++
        bodyDCircuit R.machine D word.length)
      (basisInput (a := bodyAnc R.machine D word.length) (toBits word))=
      castBodyState (by rw [bodyWidth_formula]; rfl)
        (tensorState
          (tensorState (computationalBasis (result (bodyQueryProgram R.machine) word))
            (castBodyState (queryBlocks_width_independent D _ (R.query word) [])
              (runLayered (bundleCircuit (queryBlocks D (R.machine.padding.eval word.length) (R.query word)))
                (bundleState (queryBlocks D (R.machine.padding.eval word.length) (R.query word))))))
          (computationalBasis (fun _ : Fin (4*(R.machine.padding.eval word.length+1)+1) => false))) := by
  rw [bodyFirstPhases_tensor]
  exact castBodyState_tensor_middle (queryBlocks_width_independent D _ (R.query word) [])
    _ _ _ _ _

/-- Full actual body acceptance has been pulled back through the concrete
selector and all real quantum D calls, retaining exactly their true amplitudes. -/
theorem bodyFamily_acceptance_pullback (R : QuerySpecification) (D : Family)
    (word : Str) :
    acceptProb (bodyFamily R.machine D) word=
      ∑ input : Bits (bodyPreWidth R.machine word.length+bodyDWidth R.machine D word.length),
        if multiSelectorValue (selectorBitsExtension input) (selectorBitsExtension input 0)
          (bodyChoices R.machine D word.length) then
          ‖tensorState (computationalBasis (result (bodyQueryProgram R.machine) word))
            (castBodyState (queryBlocks_width_independent D _ (R.query word) [])
              (runLayered (bundleCircuit (queryBlocks D (R.machine.padding.eval word.length) (R.query word)))
                (bundleState (queryBlocks D (R.machine.padding.eval word.length) (R.query word))))) input‖^2 else 0 := by
  change (∑ output : Bits (bodyWidth R.machine D word.length),if output
    (bodyOutput R.machine D word.length) then
    ‖runLayered (bodyCircuit R.machine D word.length)
      (basisInput (a := bodyAnc R.machine D word.length) (toBits word)) output‖^2 else 0)=_
  unfold bodyCircuit
  rw [runLayered_append_actual,bodyFirstPhases_static]
  apply multiSelector_cast_tensor_probability_scratch
  · unfold bodyPreWidth
    omega
  · have h := bodySelectorChoices_valid R.machine D word.length
    rw [bodyPreSlots_length,bodyDBundleSlots_length D _ []] at h
    exact h
  · rw [bodyChoices_length]

end Integration9_9.GenericBodySemantics

end

end P2MDyadicModule92

/- Helper module Solutions.AdvantageBridgeGenericBodyAcceptance. -/
section P2MDyadicModule93

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBodySemantics

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open Integration9_9.GenericBody

open QAlgorithms.Complexity Polynomial QMCNumericRuntime TM2PlatformSerialization

open scoped BigOperators

private theorem list_get_ofFn_eq {α : Type} {length : ℕ} (items : List α)
    (f : Fin length → α) (h : items=List.ofFn f) (index : ℕ)
    (hi : index < items.length) (hn : index < length) : items[index]=f ⟨index,hn⟩ := by
  subst items
  simp only [List.getElem_ofFn]

/-- Every emitted selector pair is the real query-length flag and the real
output address of that candidate D circuit. -/
theorem bodyChoices_get (R : QuerySpecification) (D : Family)
    (n index : ℕ) (hi : index ≤ R.machine.padding.eval n) :
    (bodyChoices R.machine D n)[index]'(by rw [bodyChoices_length]; omega)=
      ((bodyFlagAddresses R.machine (unary n))[index]'(by
        simp only [bodyFlagAddresses_length,unary,List.length_replicate]; omega),
      bodyPreWidth R.machine n+
        (bundleOutput (queryBlocks D (R.machine.padding.eval n) [])
          ⟨index,by simp only [queryBlocks,List.length_ofFn]; omega⟩).val) := by
  have htoken (hit : index < (emitDOutputs (describedQueryBlocks D (R.machine.padding.eval n))).length) :
      (emitDOutputs (describedQueryBlocks D (R.machine.padding.eval n)))[index]=
        encNat (bundleOutput (queryBlocks D (R.machine.padding.eval n) [])
          ⟨index,by simp only [queryBlocks,List.length_ofFn]; omega⟩).val :=
    list_get_ofFn_eq _ _ (emitDOutputs_correct D (R.machine.padding.eval n) []) index hit _
  have hn (number : ℕ) : QMCNumericRuntime.inputWidth (encNat number)=number := by
    rw [←unaryPayload_length,unaryPayload_number]
    simp only [unary,List.length_replicate]
  unfold bodyChoices bodySelectorChoices
  simp only [List.getElem_zip,List.getElem_map,bodyPreSlots_length,htoken,hn]
  rfl

/-- Real flags read through the retained compiler basis equal the exact query
length event, after appending an arbitrary D output register. -/
theorem bodyChoice_flag (R : QuerySpecification) (D : Family)
    (word : Str) (data : Bits (bodyDWidth R.machine D word.length)) (index : ℕ)
    (hi : index ≤ R.machine.padding.eval word.length) :
    selectorBitsExtension (Fin.append (result (bodyQueryProgram R.machine) word) data)
      ((bodyChoices R.machine D word.length)[index]'(by rw [bodyChoices_length]; omega)).1=
      decide ((R.query word).length=index) := by
  rw [bodyChoices_get R D word.length index hi]
  have hb := bodyFlagAddresses_valid R.machine word.length
    ((bodyFlagAddresses R.machine (unary word.length))[index]'(by
      simp only [bodyFlagAddresses_length,unary,List.length_replicate]; omega))
    (List.getElem_mem (by simp only [bodyFlagAddresses_length,unary,List.length_replicate]; omega))
  rw [selectorBitsExtension_append_prefix _ data _ hb]
  exact bodyFlagPointer_value R word index hi

/-- Real candidate addresses read exactly the corresponding output qubit. -/
theorem bodyChoice_output (R : QuerySpecification) (D : Family)
    (word : Str) (data : Bits (bodyDWidth R.machine D word.length)) (index : ℕ)
    (hi : index ≤ R.machine.padding.eval word.length) :
    selectorBitsExtension (Fin.append (result (bodyQueryProgram R.machine) word) data)
      ((bodyChoices R.machine D word.length)[index]'(by rw [bodyChoices_length]; omega)).2=
      data (bundleOutput (queryBlocks D (R.machine.padding.eval word.length) [])
        ⟨index,by simp only [queryBlocks,List.length_ofFn]; omega⟩) := by
  rw [bodyChoices_get R D word.length index hi]
  let output := bundleOutput (queryBlocks D (R.machine.padding.eval word.length) [])
    (⟨index,by simp only [queryBlocks,List.length_ofFn]; omega⟩ : Fin _)
  change selectorBitsExtension (Fin.append (result (bodyQueryProgram R.machine) word) data)
    (bodyPreWidth R.machine word.length+output.val)=data output
  have heq : bodyPreWidth R.machine word.length+output.val=
      (Fin.natAdd (bodyPreWidth R.machine word.length) output).val := rfl
  rw [heq,selectorBitsExtension_get]
  dsimp only [bodyPreWidth] at *
  rw [Fin.append_right]

/-- Exactly one true length flag selects the actual D output, on every basis
state of the entire D output register. -/
theorem bodySelector_value (R : QuerySpecification) (D : Family)
    (word : Str) (data : Bits (bodyDWidth R.machine D word.length))
    (hq : (R.query word).length ≤ R.machine.padding.eval word.length) :
    multiSelectorValue
      (selectorBitsExtension (Fin.append (result (bodyQueryProgram R.machine) word) data))
      (selectorBitsExtension (Fin.append (result (bodyQueryProgram R.machine) word) data) 0)
      (bodyChoices R.machine D word.length)=
      data (bundleOutput (queryBlocks D (R.machine.padding.eval word.length) [])
        ⟨(R.query word).length,by simp only [queryBlocks,List.length_ofFn]; omega⟩) := by
  apply multiSelectorValue_selected
  · intro choice hc htrue
    obtain ⟨index,hi,he⟩ := List.getElem_of_mem hc
    have himax : index ≤ R.machine.padding.eval word.length := by rw [bodyChoices_length] at hi; omega
    rw [←he,bodyChoice_flag _ _ _ _ _ himax] at htrue
    have heq : (R.query word).length=index := of_decide_eq_true htrue
    rw [←he,bodyChoice_output _ _ _ _ _ himax]
    subst index
    rfl
  · refine ⟨(bodyChoices R.machine D word.length)[(R.query word).length]'(by
      rw [bodyChoices_length]; omega),List.getElem_mem _,?_⟩
    rw [bodyChoice_flag _ _ _ _ _ hq]
    simp

end Integration9_9.GenericBodySemantics

end

end P2MDyadicModule93

/- Helper module Solutions.AdvantageBridgeGenericBodyProbability. -/
section P2MDyadicModule94

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBodySemantics

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open Integration9_9.GenericBody

open scoped BigOperators

/-- A pure physical-width cast preserves the probability of any selected wire. -/
theorem castBodyState_output_probability {left right : ℕ} (h : left=right)
    (state : QState left) (output : Fin left) :
    (∑ input : Bits right,if input (Fin.cast h output) then ‖castBodyState h state input‖^2 else 0)=
      ∑ input : Bits left,if input output then ‖state input‖^2 else 0 := by
  cases h
  rfl

/-- The actual single uniform body has exactly the queried D acceptance
probability. All other length blocks and retained work registers sum out. -/
theorem bodyFamily_acceptProb (R : QuerySpecification) (D : Family)
    (word : Str) (hq : (R.query word).length ≤ R.machine.padding.eval word.length) :
    acceptProb (bodyFamily R.machine D) word=acceptProb D (R.query word) := by
  let P := bodyQueryProgram R.machine
  let query := R.query word
  let blocks := queryBlocks D (R.machine.padding.eval word.length) query
  let changeWidth := queryBlocks_width_independent D (R.machine.padding.eval word.length) query []
  let dstate := runLayered (bundleCircuit blocks) (bundleState blocks)
  let choices := bodyChoices R.machine D word.length
  let selected : Fin (bundleWidth blocks) := bundleOutput blocks
    ⟨query.length,by dsimp only [blocks,query]; simp only [queryBlocks,List.length_ofFn]; omega⟩
  let physical : Fin (bodyDWidth R.machine D word.length) := bundleOutput (queryBlocks D (R.machine.padding.eval word.length) [])
    ⟨query.length,by dsimp only [query]; simp only [queryBlocks,List.length_ofFn]; omega⟩
  have hselected : physical=Fin.cast changeWidth selected := by
    apply Fin.ext
    exact queryBlocks_output_val_independent D (R.machine.padding.eval word.length) [] query query.length hq
  calc
    acceptProb (bodyFamily R.machine D) word=
        ∑ input : Bits (bodyPreWidth R.machine word.length+bodyDWidth R.machine D word.length),
          if multiSelectorValue (selectorBitsExtension input) (selectorBitsExtension input 0) choices then
            ‖tensorState (computationalBasis (result P word)) (castBodyState changeWidth dstate) input‖^2 else 0 :=
      bodyFamily_acceptance_pullback R D word
    _=∑ input : Bits (bodyDWidth R.machine D word.length),
        if multiSelectorValue (selectorBitsExtension (Fin.append (result P word) input))
          (selectorBitsExtension (Fin.append (result P word) input) 0) choices then
          ‖castBodyState changeWidth dstate input‖^2 else 0 :=
      basisTensor_event_probability (result P word) (castBodyState changeWidth dstate) _
    _=∑ input : Bits (bodyDWidth R.machine D word.length),
        if input physical then ‖castBodyState changeWidth dstate input‖^2 else 0 := by
      apply Finset.sum_congr rfl
      intro input _
      have he := bodySelector_value R D word input hq
      exact congrArg (fun value : Bool => if value then ‖castBodyState changeWidth dstate input‖^2 else 0) he
    _=∑ input : Bits (bundleWidth blocks),if input selected then ‖dstate input‖^2 else 0 := by
      exact (congrArg (fun wire : Fin (bodyDWidth R.machine D word.length) =>
        ∑ input : Bits (bodyDWidth R.machine D word.length),if input wire then
          ‖castBodyState changeWidth dstate input‖^2 else 0) hselected).trans
        (castBodyState_output_probability changeWidth dstate selected)
    _=acceptProb D query := queryBlocks_selected_probability D (R.machine.padding.eval word.length) query hq

/-- Every proved polynomial query specification gives unconditional exact
acceptance for the actual full uniform body. -/
theorem bodyFamily_actual_acceptProb (R : QuerySpecification) (D : Family) (word : Str) :
    acceptProb (GenericBody.bodyFamily R.machine D) word=acceptProb D (R.query word) :=
  bodyFamily_acceptProb R D word (R.query_bound word)

end Integration9_9.GenericBodySemantics

end

end P2MDyadicModule94

/- Helper module Solutions.AdvantageBridgeRetainedCoins. -/
section P2MDyadicModule95

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

/-- Full classical reversible compilation preserves every wire outside the
Boolean assignment targets, even on arbitrary garbage input. -/
theorem BooleanGate.compile_preserves_wire {width : ℕ} (gate : BooleanGate width)
    (state : Bits width) (wire : Fin width) (h : wire ≠ gate.target) :
    reversibleAction gate.compile state wire=state wire := by
  cases gate with
  | constant target bit =>
    cases bit <;> simp_all [BooleanGate.compile,BooleanGate.target,reversibleAction,
      ReversibleGate.equiv,ReversibleGate.act,Function.update_of_ne]
  | copy source target distinct =>
    simp_all [BooleanGate.compile,BooleanGate.target,reversibleAction,
      ReversibleGate.equiv,ReversibleGate.act,Function.update_of_ne]
  | negate source target distinct =>
    simp_all [BooleanGate.compile,BooleanGate.target,reversibleAction,
      ReversibleGate.equiv,ReversibleGate.act,Function.update_of_ne]
  | xor first second target distinctFirst distinctSecond =>
    simp_all [BooleanGate.compile,BooleanGate.target,reversibleAction,
      ReversibleGate.equiv,ReversibleGate.act,Function.update_of_ne]
  | and first second target distinctFirst distinctSecond =>
    by_cases hs : first=second
    · simp_all [BooleanGate.compile,BooleanGate.target,reversibleAction,
        ReversibleGate.equiv,ReversibleGate.act,Function.update_of_ne]
    · simp_all [BooleanGate.compile,BooleanGate.target,reversibleAction,
        ReversibleGate.equiv,ReversibleGate.act,Function.update_of_ne]

/-- A whole genuine reversible Boolean program retains all read-only labels. -/
theorem booleanToReversible_preserves_wire {width : ℕ} (gates : List (BooleanGate width))
    (state : Bits width) (wire : Fin width) (h : ∀ gate∈gates,wire ≠ gate.target) :
    reversibleAction (booleanToReversible gates) state wire=state wire := by
  induction gates generalizing state with
  | nil => rfl
  | cons gate rest ih =>
    simp only [booleanToReversible,List.flatMap_cons,reversibleAction_append,Equiv.trans_apply]
    change (reversibleAction (booleanToReversible rest)) ((reversibleAction gate.compile) state) wire=state wire
    rw [ih _ (fun other ho => h other (by simp [ho]))]
    exact gate.compile_preserves_wire state wire (h gate (by simp))

/-- The inverse permutation also preserves every actual read-only wire. -/
theorem booleanToReversible_inverse_preserves_wire {width : ℕ} (gates : List (BooleanGate width))
    (state : Bits width) (wire : Fin width) (h : ∀ gate∈gates,wire ≠ gate.target) :
    (reversibleAction (booleanToReversible gates)).symm state wire=state wire := by
  have hf := booleanToReversible_preserves_wire gates
    ((reversibleAction (booleanToReversible gates)).symm state) wire h
  simpa only [Equiv.apply_symm_apply] using hf.symm

/-- Orthogonal retained classical coin labels remove every interference term.
This applies to arbitrary genuine quantum output amplitudes, including garbage. -/
theorem retainedCoins_event_probability {coins width : ℕ}
    (label : Bits width → Bits coins) (branches : Bits coins → QState width)
    (hsupport : ∀ coin input,branches coin input ≠ 0 → label input=coin)
    (event : Bits width → Bool) :
    (∑ input : Bits width,if event input then
      ‖(∑ coin : Bits coins,coinAmplitude coins • branches coin) input‖^2 else 0)=
      avg (fun coin : Bits coins => ∑ input : Bits width,if event input then ‖branches coin input‖^2 else 0) := by
  classical
  have hzero (input : Bits width) (coin : Bits coins) (hne : coin ≠ label input) : branches coin input=0 := by
    by_contra hn
    exact hne (hsupport coin input hn).symm
  have hpoint (input : Bits width) :
      (if event input then ‖(∑ coin : Bits coins,coinAmplitude coins • branches coin) input‖^2 else 0)=
        (Fintype.card (Bits coins) : ℝ)⁻¹*
          ∑ coin : Bits coins,if event input then ‖branches coin input‖^2 else 0 := by
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_eq_single (label input)]
    · rw [Finset.sum_eq_single (label input)]
      · cases event input <;> simp [norm_mul,mul_pow,coinAmplitude_mass]
      · intro coin _ hne
        simp [hzero input coin hne]
      · simp
    · intro coin _ hne
      rw [hzero input coin hne,mul_zero]
    · simp
  simp only [hpoint,←Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold avg
  ring

end InfoLossLAR.WorstCase

end P2MDyadicModule95

/- Helper module Solutions.AdvantageBridgeGenericBodyInputSupport. -/
section P2MDyadicModule96

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBodySemantics

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open Integration9_9.GenericBody

/-- Any nonzero tensor amplitude has its literal retained basis prefix. -/
theorem castTensorBasis_prefix {first middle last total : ℕ}
    (h : (first+middle)+last=total) (bits : Bits first)
    (middleState : QState middle) (lastState : QState last)
    (input : Bits total)
    (hn : castBodyState h (tensorState (tensorState (computationalBasis bits) middleState) lastState) input ≠ 0)
    (index : Fin first) :
    input (Fin.cast h (Fin.castAdd last (Fin.castAdd middle index)))=bits index := by
  cases h
  have he : leftRegister (leftRegister input)=bits := by
    by_contra hne
    apply hn
    simp [castBodyState,tensorState,computationalBasis,hne]
  exact congrFun he index

/-- The real first two phases retain every original classical input bit. -/
theorem bodyFirstPhases_input_support (R : QuerySpecification) (D : Family)
    (word : Str) (input : Bits (bodyWidth R.machine D word.length))
    (hn : runLayered
      (compileReversible (booleanToReversible (bodyPreparedGates R.machine D word.length))++
        bodyDCircuit R.machine D word.length)
      (basisInput (a := bodyAnc R.machine D word.length) (toBits word)) input ≠ 0)
    (index : Fin word.length) :
    input ⟨index.val,by unfold bodyWidth; omega⟩=toBits word index := by
  rw [bodyFirstPhases_static] at hn
  let cell : Fin (bodyPreWidth R.machine word.length) :=
    ⟨index.val,by unfold bodyPreWidth; omega⟩
  have hp := castTensorBasis_prefix _ _ _ _ input hn cell
  refine hp.trans ?_
  change BooleanProgram.run word.length (compiled (bodyQueryProgram R.machine) word.length).ops
    (wordExtension word) index.val=toBits word index
  rw [BooleanProgram.run_below _ _ _ _ index.isLt,wordExtension_before word index.val index.isLt]
  rfl

/-- The complete actual body retains its classical input labels even after
quantum D computation and the genuine reversible output selector. -/
theorem bodyFamily_input_support (R : QuerySpecification) (D : Family)
    (word : Str) (input : Bits (bodyWidth R.machine D word.length))
    (hn : runLayered (bodyCircuit R.machine D word.length)
      (basisInput (a := bodyAnc R.machine D word.length) (toBits word)) input ≠ 0)
    (index : Fin word.length) :
    input ⟨index.val,by unfold bodyWidth; omega⟩=toBits word index := by
  let gates := bodySelectorGates R.machine D word.length
  let wire : Fin (bodyWidth R.machine D word.length) := ⟨index.val,by unfold bodyWidth; omega⟩
  have htarget : ∀ gate∈gates,wire ≠ gate.target := by
    intro gate hg he
    have hr := BooleanProgram.target_range
      (multiSelectorOps (bodyPreWidth R.machine word.length+bodyDWidth R.machine D word.length)
        0 (bodyChoices R.machine D word.length))
      (by simpa only [multiSelectorOps_length] using bodySelected_bound R.machine D word.length) gate hg
    have hv := congrArg Fin.val he
    dsimp only [wire] at hv
    unfold bodyPreWidth at hr
    omega
  have hretain := booleanToReversible_inverse_preserves_wire gates input wire htarget
  unfold bodyCircuit at hn
  rw [runLayered_append_actual,compileReversible_apply] at hn
  have hbefore := bodyFirstPhases_input_support R D word
    ((reversibleAction (booleanToReversible gates)).symm input) hn index
  exact hretain.symm.trans hbefore

end Integration9_9.GenericBodySemantics

end

end P2MDyadicModule96

/- Helper module Solutions.AdvantageBridgeRandomizedFamily. -/
section P2MDyadicModule97

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.RandomizedCircuit

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open Integration9_9.LARCoinLayout

open QAlgorithms.Complexity Polynomial

theorem family_wellFormed (coins : Polynomial ℕ) (F : Family) (hF : WellFormed F) :
    WellFormed (family coins F) := by
  intro n layer hl
  simp only [family,circuit,List.mem_append] at hl
  rcases hl with (hc|hh)|hq
  · exact compileReversible_wellFormed _ layer hc
  · exact castBodyCircuit_wellFormed _ _ (rightCircuit_wellFormed _
      (leftCircuit_wellFormed _ (coinCircuit_wellFormed _))) layer hh
  · exact castBodyCircuit_wellFormed _ _ (rightCircuit_wellFormed _ (hF _)) layer hq

theorem circuit_depth (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    depth (circuit coins F n) ≤ 74*(workLength coins n)+coins.eval n+depth (F.circ (workLength coins n)) := by
  unfold circuit
  rw [show depth (compileReversible (booleanToReversible (copyGates coins F n))++
      hadamardCircuit coins F n++queryCircuit coins F n)=
    depth (compileReversible (booleanToReversible (copyGates coins F n)))+
      depth (hadamardCircuit coins F n)+depth (queryCircuit coins F n) by simp [depth,List.length_append,Nat.add_assoc]]
  have hcopy := BooleanProgram.circuit_depth (registerLoadOps (copySources coins n))
    (by rw [registerLoadOps_length,copySources_length]; unfold workLength width ancillary; omega :
      n+(registerLoadOps (copySources coins n)).length ≤ width coins F n)
  change depth (compileReversible (booleanToReversible (copyGates coins F n))) ≤ _ at hcopy
  rw [registerLoadOps_length,copySources_length] at hcopy
  simp only [hadamardCircuit,queryCircuit,castBodyCircuit_depth,leftCircuit_depth,rightCircuit_depth,coinCircuit_depth]
  omega

/-- A single explicit polynomial bounds both actual outer depth and ancillas. -/
theorem family_polyBounded (coins : Polynomial ℕ) (F : Family) (hF : PolyBounded F) :
    PolyBounded (family coins F) := by
  obtain ⟨p,hp⟩ := hF
  refine ⟨C 75*(coins+X)+p.comp (coins+X),?_⟩
  constructor
  · intro n
    have hd := circuit_depth coins F n
    have hf := hp.1 (workLength coins n)
    simp only [eval_add,eval_mul,eval_C,eval_X,eval_comp]
    change depth (circuit coins F n) ≤ 75*(coins.eval n+n)+p.eval (coins.eval n+n)
    unfold workLength at hd hf
    omega
  · intro n
    have hf := hp.2 (workLength coins n)
    simp only [eval_add,eval_mul,eval_C,eval_X,eval_comp]
    change ancillary coins F n ≤ 75*(coins.eval n+n)+p.eval (coins.eval n+n)
    unfold ancillary workLength at *
    omega

end Integration9_9.RandomizedCircuit

end

end P2MDyadicModule97

/- Helper module Solutions.AdvantageBridgeRandomizedPreparation. -/
section P2MDyadicModule98

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.RandomizedCircuit

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open Integration9_9.LARCoinLayout

open QAlgorithms.Complexity Polynomial

open scoped BigOperators

/-- Width of the original word, coin register, copied word, and zero workspace. -/
theorem preparation_width (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    n+(coins.eval n+(n+(F.anc (workLength coins n)+1)))=width coins F n := by
  unfold width ancillary
  omega

/-- The literal copy circuit prepares exactly its existing operational value
vector, preserving the original input and every later zero scratch position. -/
theorem copy_basis (coins : Polynomial ℕ) (F : Family) (word : Str) :
    runLayered (compileReversible (booleanToReversible (copyGates coins F word.length)))
      (basisInput (a := ancillary coins F word.length) (toBits word))=
      computationalBasis (fun index => inputCopyResult word (coins.eval word.length) index.val) :=
  inputCopy_circuit_basis word (coins.eval word.length) (F.anc (workLength coins word.length))

/-- The actual copy circuit prepares a retained original, fair-bit zero slots,
and an exact word/ancilla basis for the later coin-first body input. -/
theorem copy_tensor (coins : Polynomial ℕ) (F : Family) (word : Str) :
    computationalBasis (fun index : Fin (width coins F word.length) =>
      inputCopyResult word (coins.eval word.length) index.val)=
      castBodyState (preparation_width coins F word.length)
        (tensorState (computationalBasis (toBits word))
          (tensorState (coinZero (coins.eval word.length))
            (basisInput (a := F.anc (workLength coins word.length)) (toBits word)))) := by
  change _=castBodyState _ (tensorState (computationalBasis (toBits word))
    (tensorState (computationalBasis (fun _ => false))
      (basisInput (a := F.anc (workLength coins word.length)) (toBits word))))
  rw [basisInput_eq_computationalBasis,wordExtension_basis,
    ←computationalBasis_tensor,←computationalBasis_tensor,castBodyState_basis]
  apply congrArg computationalBasis
  have hp (index : Fin (word.length+(coins.eval word.length+
      (word.length+(F.anc (workLength coins word.length)+1))))) :
      inputCopyResult word (coins.eval word.length) index.val=
        Fin.append (toBits word) (Fin.append (fun _ => false) (fun i => wordExtension word i.val)) index := by
    refine Fin.addCases (fun original => ?_) (fun work => ?_) index
    · simp only [Fin.val_castAdd,Fin.append_left,inputCopyResult,if_pos original.isLt]
      rw [wordExtension_before word original.val original.isLt]
      rfl
    · refine Fin.addCases (fun coin => ?_) (fun body => ?_) work
      · simp (disch := omega) only [Fin.val_natAdd,Fin.val_castAdd,Fin.append_right,Fin.append_left,
          inputCopyResult,if_neg,if_pos]
      · simp only [Fin.val_natAdd,Fin.append_right]
        by_cases hi : body.val < word.length
        · simp (disch := omega) only [inputCopyResult,if_neg,if_pos]
          congr 1
          omega
        · rw [wordExtension_after word body.val (by omega)]
          simp (disch := omega) only [inputCopyResult,if_neg]
  funext index
  simpa only [Fin.val_cast] using hp (Fin.cast (preparation_width coins F word.length).symm index)

/-- The actual copy and H phases prepare positive uniform coin amplitudes,
with no measurement, and retain an untouched original word. -/
theorem hadamard_tensor (coins : Polynomial ℕ) (F : Family) (word : Str) :
    runLayered
      (compileReversible (booleanToReversible (copyGates coins F word.length))++hadamardCircuit coins F word.length)
      (basisInput (a := ancillary coins F word.length) (toBits word))=
      castBodyState (preparation_width coins F word.length)
        (tensorState (computationalBasis (toBits word))
          (tensorState (fun _ => coinAmplitude (coins.eval word.length))
            (basisInput (a := F.anc (workLength coins word.length)) (toBits word)))) := by
  rw [runLayered_append_actual,copy_basis,copy_tensor]
  unfold hadamardCircuit
  rw [runLayered_castBody,rightCircuit_tensor,leftCircuit_tensor,coinCircuit_uniform]

end Integration9_9.RandomizedCircuit

end

end P2MDyadicModule98

/- Helper module Solutions.AdvantageBridgeRandomizedBranches. -/
section P2MDyadicModule99

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.RandomizedCircuit

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open Integration9_9.LARCoinLayout

open QAlgorithms.Complexity Polynomial

open scoped BigOperators

theorem query_width (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    n+(workLength coins n+(F.anc (workLength coins n)+1))=width coins F n := by
  unfold width ancillary workLength
  omega

theorem castBodyState_sum {left right : ℕ} {α : Type} [Fintype α] (h : left=right)
    (states : α → QState left) :
    castBodyState h (∑ index,states index)=∑ index,castBodyState h (states index) := by cases h; rfl

theorem castBodyState_smul {left right : ℕ} (h : left=right) (scalar : ℂ) (state : QState left) :
    castBodyState h (scalar • state)=scalar • castBodyState h state := by cases h; rfl

theorem castBodyState_tensor_right {prefixSize left right total : ℕ}
    (h : left=right) (hl : prefixSize+left=total) (hr : prefixSize+right=total)
    (prefixState : QState prefixSize) (state : QState left) :
    castBodyState hl (tensorState prefixState state)=
      castBodyState hr (tensorState prefixState (castBodyState h state)) := by cases h; rfl

/-- The true H-prepared body input is a sum of positive equal-amplitude actual
classical coin-first input basis states. -/
theorem coherentInput_sum (coins : Polynomial ℕ) (F : Family) (word : Str) :
    coherentInput coins F word=
      ∑ coin : Bits (coins.eval word.length),coinAmplitude (coins.eval word.length) • branchInput coins F word coin := by
  unfold coherentInput branchInput
  rw [basisInput_eq_computationalBasis]
  change castBodyState _ (coinBranchState
    (fun _ => computationalBasis (Fin.append (toBits word) (fun _ => false))))=_
  rw [coinBasisBranch_sum,castBodyState_sum]
  apply Finset.sum_congr rfl
  intro coin _
  exact castBodyState_smul _ _ _

/-- The true body circuit acts linearly in every classical-coin branch. -/
theorem coherentOutput_sum (coins : Polynomial ℕ) (F : Family) (word : Str) :
    runLayered (F.circ (workLength coins word.length)) (coherentInput coins F word)=
      ∑ coin : Bits (coins.eval word.length),coinAmplitude (coins.eval word.length) • branchOutput coins F word coin := by
  rw [coherentInput_sum,←runLayeredLinearMap_apply,map_sum]
  simp only [map_smul,runLayeredLinearMap_apply,branchOutput]

/-- The complete actual outer circuit produces a retained original word and
the actual coherent sum of all queried body output states. -/
theorem circuit_tensor (coins : Polynomial ℕ) (F : Family) (word : Str) :
    runLayered (circuit coins F word.length)
      (basisInput (a := ancillary coins F word.length) (toBits word))=
      castBodyState (query_width coins F word.length)
        (tensorState (computationalBasis (toBits word))
          (∑ coin : Bits (coins.eval word.length),
            coinAmplitude (coins.eval word.length) • branchOutput coins F word coin)) := by
  unfold circuit
  rw [runLayered_append_actual,hadamard_tensor]
  have ht := castBodyState_tensor_right (work_width coins F word.length)
    (preparation_width coins F word.length) (query_width coins F word.length)
    (computationalBasis (toBits word))
    (tensorState (fun _ => coinAmplitude (coins.eval word.length))
      (basisInput (a := F.anc (workLength coins word.length)) (toBits word)))
  rw [ht]
  unfold queryCircuit
  rw [runLayered_castBody,rightCircuit_tensor]
  exact congrArg (fun state => castBodyState (query_width coins F word.length)
    (tensorState (computationalBasis (toBits word)) state)) (coherentOutput_sum coins F word)

end Integration9_9.RandomizedCircuit

end

end P2MDyadicModule99

/- Helper module Solutions.AdvantageBridgeRandomizedBranchBasis. -/
section P2MDyadicModule100

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.RandomizedCircuit

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open Integration9_9.LARCoinLayout

open QAlgorithms.Complexity Polynomial

open scoped BigOperators

/-- Every true branch input is exactly the encoded classical coin-first word,
with all workspace bits zero, expressed on the already fixed body width. -/
theorem branchInput_wordExtension (coins : Polynomial ℕ) (F : Family) (word : Str)
    (coin : Bits (coins.eval word.length)) :
    branchInput coins F word coin=computationalBasis
      (fun index => wordExtension (List.ofFn coin++word) index.val) := by
  unfold branchInput
  rw [castBodyState_basis]
  apply congrArg computationalBasis
  have hp (index : Fin (coins.eval word.length+(word.length+(F.anc (workLength coins word.length)+1)))) :
      Fin.append coin (Fin.append (toBits word) (fun _ => false)) index=
        wordExtension (List.ofFn coin++word) index.val := by
    rw [wordExtension_basis]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) index
    · simp only [Fin.append_left,Fin.val_castAdd,wordExtension]
      rw [List.getElem?_append_left (by simp only [List.length_ofFn]; exact i.isLt)]
      simp only [List.getElem?_ofFn,dif_pos i.isLt,Option.getD_some]
    · simp only [Fin.append_right,Fin.val_natAdd,wordExtension]
      rw [List.getElem?_append_right (by simp only [List.length_ofFn]; omega)]
      simp only [List.length_ofFn,Nat.add_sub_cancel_left]
  funext index
  simpa only [Fin.val_cast] using hp (Fin.cast (work_width coins F word.length).symm index)

/-- The literal platform acceptance probability may be evaluated at any equal
input length, using the complete word/zero basis vector. -/
theorem acceptProb_at_length (F : Family) (word : Str) (length : ℕ) (hlen : word.length=length) :
    (∑ input : Bits (length+(F.anc length+1)),if input (F.out length) then
      ‖runLayered (F.circ length) (computationalBasis (fun index => wordExtension word index.val)) input‖^2 else 0)=
      acceptProb F word := by
  subst length
  unfold acceptProb
  rw [basisInput_eq_computationalBasis,wordExtension_basis]

/-- Each actual quantum branch has exactly F's original classical-input
acceptance probability, without extra postprocessing or conditioning. -/
theorem branchOutput_probability (coins : Polynomial ℕ) (F : Family) (word : Str)
    (coin : Bits (coins.eval word.length)) :
    (∑ input : Bits (workLength coins word.length+(F.anc (workLength coins word.length)+1)),
      if input (F.out (workLength coins word.length)) then ‖branchOutput coins F word coin input‖^2 else 0)=
      acceptProb F (List.ofFn coin++word) := by
  unfold branchOutput
  rw [branchInput_wordExtension]
  exact acceptProb_at_length F (List.ofFn coin++word) (workLength coins word.length)
    (by simp only [List.length_append,List.length_ofFn,workLength])

/-- The read-only input support property is insensitive to an equal length. -/
theorem inputSupport_at_length (F : Family) (hF : PreservesClassicalInput F)
    (word : Str) (length : ℕ) (hlen : word.length=length)
    (output : Bits (length+(F.anc length+1)))
    (hn : runLayered (F.circ length) (computationalBasis (fun index => wordExtension word index.val)) output ≠ 0)
    (index : ℕ) (hi : index < word.length) :
    output ⟨index,by omega⟩=wordExtension word index := by
  subst length
  have h := hF word output
  rw [basisInput_eq_computationalBasis,wordExtension_basis] at h
  have hv := h hn ⟨index,hi⟩
  rw [wordExtension_before word index hi]
  exact hv

/-- The true body circuit retains its own original coin label in every
nonzero branch amplitude, so all different coin branches are orthogonal. -/
theorem branchOutput_coin_support (coins : Polynomial ℕ) (F : Family) (hF : PreservesClassicalInput F)
    (word : Str) (coin : Bits (coins.eval word.length))
    (output : Bits (workLength coins word.length+(F.anc (workLength coins word.length)+1)))
    (hn : branchOutput coins F word coin output ≠ 0) :
    coinLabel coins F word.length output=coin := by
  unfold branchOutput at hn
  rw [branchInput_wordExtension] at hn
  funext index
  have hs := inputSupport_at_length F hF (List.ofFn coin++word) (workLength coins word.length)
    (by simp only [List.length_append,List.length_ofFn,workLength]) output hn index.val
    (by simp only [List.length_append,List.length_ofFn]; omega)
  change output ⟨index.val,_⟩=coin index
  refine hs.trans ?_
  unfold wordExtension
  rw [List.getElem?_append_left (by simp only [List.length_ofFn]; exact index.isLt)]
  simp only [List.getElem?_ofFn,dif_pos index.isLt,Option.getD_some]

end Integration9_9.RandomizedCircuit

end

end P2MDyadicModule100

/- Helper module Solutions.AdvantageBridgeUniformRequest. -/
section P2MDyadicModule101

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 Integration9_9.TM2StockLists

/-- A real native request and descriptor builder can call an arbitrary original
uniform stock generator, preserving the untouched input alongside the result.
No restriction on the generator's private alphabet is introduced. -/
theorem uniformRequest_builder_polyTime (F : Family) (hF : Uniform F)
    (request : Str → Str) (hrequest : Poly request) (size : ℕ → ℕ)
    (hsize : ∀ word,request word=unary (size word.length))
    (builder : Str × Str → Str) (hbuilder : Poly builder) :
    PolyTimeComputable (fun word : Str => builder (word,encFamilyAt F (size word.length))) := by
  obtain ⟨source,⟨sourceProgram⟩,hsource⟩ := hF
  let requestProgram := LARCoinLayout.rawPolyProgram (f := request) hrequest
  obtain ⟨called⟩ := TM2Composition.comp requestProgram.stock sourceProgram
  obtain ⟨quoted⟩ := stock_quoted called
  obtain ⟨paired⟩ := stock_pairWithInput quoted
  obtain ⟨encoded⟩ := TM2Composition.comp BooleanLists.packProgram.stock paired
  obtain ⟨built⟩ := TM2Composition.comp encoded hbuilder.program.stock
  obtain ⟨whole⟩ := TM2Composition.comp built BooleanLists.unpackProgram.stock
  refine ⟨congrProgram whole _ ?_⟩
  intro word
  simp only [Function.comp_apply,id_eq]
  rw [hsize,hsource]

end InfoLossLAR.WorstCase

end P2MDyadicModule101

/- Helper module Solutions.AdvantageBridgeRandomizedUniform. -/
section P2MDyadicModule102

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.RandomizedCircuit

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open Integration9_9.LARCoinLayout

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime TM2PlatformSerialization

@[fun_prop] theorem ancillarySlots_poly (coins : Polynomial ℕ) :
    Poly (fun x : Str × Str => ancillarySlots coins x.1 x.2) := by
  unfold ancillarySlots
  fun_prop

theorem ancillarySlots_length (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    (ancillarySlots coins (unary n) (encFamilyAt F (workLength coins n))).length=ancillary coins F n := by
  unfold ancillarySlots encFamilyAt
  simp only [List.append_assoc,unaryPayload_encNat,List.length_append,List.length_map,
    queryWireSlots_length,unary,List.length_replicate]
  unfold ancillary
  omega

@[fun_prop] theorem allSlots_poly (coins : Polynomial ℕ) :
    Poly (fun x : Str × Str => allSlots coins x.1 x.2) := by
  unfold allSlots
  fun_prop

theorem allSlots_length (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    (allSlots coins (unary n) (encFamilyAt F (workLength coins n))).length=width coins F n := by
  simp only [allSlots,List.length_append,List.length_map,List.length_singleton]
  rw [ancillarySlots_length]
  simp only [unary,List.length_replicate,width]
  omega

@[fun_prop] theorem copyWords_poly (coins : Polynomial ℕ) :
    Poly (fun x : Str × Str => copyWords coins x.1 x.2) := by
  unfold copyWords
  fun_prop

theorem copyWords_correct (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    copyWords coins (unary n) (encFamilyAt F (workLength coins n))=
      (copyGates coins F n).map BooleanGate.code := by
  unfold copyWords
  have hn : n+(coins.eval n+n) ≤ width coins F n := by unfold width ancillary; omega
  have h := inputCopyGateWords_correct
    (allSlots coins (unary n) (encFamilyAt F (workLength coins n)))
    (queryWireSlots coins (unary n)) ((unary n).map (fun _ => ()))
    (by simpa only [queryWireSlots_length,unary,List.length_replicate,List.length_map] using hn :
      ((unary n).map (fun _ => ())).length+
        ((queryWireSlots coins (unary n)).length+((unary n).map (fun _ => ())).length) ≤ width coins F n)
    (by rw [allSlots_length]; simpa only [queryWireSlots_length,unary,List.length_replicate,List.length_map] using hn)
  convert h using 1
  simp only [queryWireSlots,unary,List.length_replicate,List.map_replicate,copyGates,copySources]

@[fun_prop] theorem copyDescription_poly (coins : Polynomial ℕ) :
    Poly (fun x : Str × Str => copyDescription coins x.1 x.2) := by
  unfold copyDescription
  fun_prop

theorem copyDescription_correct (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    copyDescription coins (unary n) (encFamilyAt F (workLength coins n))=(copyBooleanFamily coins F).code n := by
  unfold copyDescription
  rw [lengthToken_eq,ancillarySlots_length,copyWords_correct,serializeWords_eq]
  rfl

@[fun_prop] theorem copyQuantumDescription_poly (coins : Polynomial ℕ) :
    Poly (fun x : Str × Str => copyQuantumDescription coins x.1 x.2) := by
  unfold copyQuantumDescription
  fun_prop

theorem copyQuantumDescription_correct (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    copyQuantumDescription coins (unary n) (encFamilyAt F (workLength coins n))=
      encFamilyAt (copyBooleanFamily coins F).reversible.compile n := by
  unfold copyQuantumDescription
  rw [copyDescription_correct,compileBooleanDescription_code,compileReversibleDescription_code]

@[fun_prop] theorem hadamardWords_poly (coins : Polynomial ℕ) : Poly (hadamardWords coins) := by
  unfold hadamardWords
  fun_prop

private theorem rightLeft_words {left middle right : ℕ} (c : Layered middle) :
    (rightCircuit (n := left) (leftCircuit (m := right) c)).map (List.map encInstr)=
      (rightCircuit (n := left) c).map (List.map encInstr) := by
  have he (gate : Instr middle) :
      encInstr (rightInstruction (n := left) (leftInstruction (m := right) gate))=
        encInstr (rightInstruction (n := left) gate) := by cases gate <;> rfl
  simp only [leftCircuit,rightCircuit,List.map_map,Function.comp_def,he]

theorem hadamardWords_correct (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    hadamardWords coins (unary n)=(hadamardCircuit coins F n).map (List.map encInstr) := by
  unfold hadamardWords
  rw [coinCircuitDescription_correct]
  have hlen : ((queryWireSlots coins (unary n)).map (fun _ => true)).length=coins.eval n := by
    rw [List.length_map,queryWireSlots_length]
    simp only [unary,List.length_replicate]
  rw [hlen]
  have hr := readCircuitLayers_append (coinCircuit (coins.eval n)) []
  simp only [List.append_nil] at hr
  rw [hr]
  simp only
  rw [shiftCircuitWords_correct]
  unfold hadamardCircuit
  rw [castBodyCircuit_instructionWords,rightLeft_words]
  apply rightCircuit_instructionWords_congr
  simp [unary]

@[fun_prop] theorem queryWords_poly : Poly (fun x : Str × Str => queryWords x.1 x.2) := by
  unfold queryWords
  fun_prop

theorem queryWords_correct (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    queryWords (unary n) (encFamilyAt F (workLength coins n))=(queryCircuit coins F n).map (List.map encInstr) := by
  unfold queryWords
  rw [readFamilyCircuitLayers_correct,shiftCircuitWords_correct]
  unfold queryCircuit
  rw [castBodyCircuit_instructionWords]
  apply rightCircuit_instructionWords_congr
  simp [unary]

@[fun_prop] theorem outputWord_poly (coins : Polynomial ℕ) :
    Poly (fun x : Str × Str => outputWord coins x.1 x.2) := by
  unfold outputWord
  fun_prop

theorem outputWord_correct (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    outputWord coins (unary n) (encFamilyAt F (workLength coins n))=encNat (output coins F n).val := by
  unfold outputWord
  rw [queryWireRequest_unary]
  change shiftWireWord (unary n) (readFamilyFrame (unary (workLength coins n),_)).2.1=_
  rw [readFamilyFrame_correct,shiftWireWord_spec]
  rw [←unaryPayload_length,unaryPayload_number]
  simp only [unary,List.length_replicate,output]

attribute [local irreducible] copyQuantumDescription hadamardWords queryWords

@[fun_prop] theorem description_poly (coins : Polynomial ℕ) :
    Poly (fun x : Str × Str => description coins x.1 x.2) := by
  unfold description
  fun_prop

theorem description_correct (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    description coins (unary n) (encFamilyAt F (workLength coins n))=encFamilyAt (family coins F) n := by
  unfold description
  rw [lengthToken_eq,ancillarySlots_length,outputWord_correct,copyQuantumDescription_correct,
    readFamilyCircuitLayers_correct,hadamardWords_correct,queryWords_correct]
  change _=encNat (ancillary coins F n)++encNat (output coins F n).val++encCirc (circuit coins F n)
  unfold circuit
  simp only [serializeWords_eq,encCirc,List.map_append,List.map_map,Function.comp_def]
  rfl

theorem family_uniform (coins : Polynomial ℕ) (F : Family) (hF : Uniform F) : Uniform (family coins F) := by
  let generator := fun word : Str => description coins word (encFamilyAt F (workLength coins word.length))
  refine ⟨generator,uniformRequest_builder_polyTime F hF (queryWireRequest coins)
    (queryWireRequest_poly coins) (workLength coins) ?_ _ (description_poly coins),?_⟩
  · intro word
    simp only [queryWireRequest,List.length_map,eval_add,eval_X,List.map_replicate,unary,workLength]
  · intro n
    dsimp only [generator]
    simpa only [unary,List.length_replicate] using description_correct coins F n

/-- Actual uniform quantum randomization, with a genuine raw TM2 generator. -/
theorem family_isQPT (coins : Polynomial ℕ) (F : Family) (hF : IsQPT F) : IsQPT (family coins F) :=
  ⟨family_uniform coins F hF.1,family_wellFormed coins F hF.2.1,family_polyBounded coins F hF.2.2⟩

end Integration9_9.RandomizedCircuit

end

end P2MDyadicModule102

/- Helper module Solutions.AdvantageBridgeRandomizedProbability. -/
section P2MDyadicModule103

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.RandomizedCircuit

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open Integration9_9.LARCoinLayout

open QAlgorithms.Complexity Polynomial

open scoped BigOperators

/-- Exact acceptance of the actual uniform randomized family: real H-coins
and the coherent full body produce precisely the classical uniform average. -/
theorem family_acceptProb (coins : Polynomial ℕ) (F : Family) (hF : PreservesClassicalInput F) (word : Str) :
    acceptProb (family coins F) word=
      avg (fun coin : Bits (coins.eval word.length) => acceptProb F (List.ofFn coin++word)) := by
  let branches := branchOutput coins F word
  let superposition := ∑ coin : Bits (coins.eval word.length),coinAmplitude (coins.eval word.length) • branches coin
  have hcast := castBodyState_output_probability (query_width coins F word.length)
    (tensorState (computationalBasis (toBits word)) superposition)
    (Fin.natAdd word.length (F.out (workLength coins word.length)))
  have hnorm :
      (∑ input : Bits (word.length+(workLength coins word.length+(F.anc (workLength coins word.length)+1))),
        if input (Fin.natAdd word.length (F.out (workLength coins word.length))) then
          ‖tensorState (computationalBasis (toBits word)) superposition input‖^2 else 0)=
      ∑ input : Bits (workLength coins word.length+(F.anc (workLength coins word.length)+1)),
        if input (F.out (workLength coins word.length)) then ‖superposition input‖^2 else 0 := by
    simpa only [Fin.append_right] using
      basisTensor_event_probability (toBits word) superposition
        (fun input => input (Fin.natAdd word.length (F.out (workLength coins word.length))))
  calc
    acceptProb (family coins F) word=
        ∑ input : Bits (width coins F word.length),if input (output coins F word.length) then
          ‖castBodyState (query_width coins F word.length)
            (tensorState (computationalBasis (toBits word)) superposition) input‖^2 else 0 := by
      change (∑ input : Bits (width coins F word.length),if input (output coins F word.length) then
        ‖runLayered (circuit coins F word.length)
          (basisInput (a := ancillary coins F word.length) (toBits word)) input‖^2 else 0)=_
      rw [circuit_tensor]
    _=∑ input : Bits (workLength coins word.length+(F.anc (workLength coins word.length)+1)),
        if input (F.out (workLength coins word.length)) then ‖superposition input‖^2 else 0 := hcast.trans hnorm
    _=avg (fun coin : Bits (coins.eval word.length) =>
        ∑ input : Bits (workLength coins word.length+(F.anc (workLength coins word.length)+1)),
          if input (F.out (workLength coins word.length)) then ‖branches coin input‖^2 else 0) :=
      retainedCoins_event_probability (coinLabel coins F word.length) branches
        (branchOutput_coin_support coins F hF word) (fun input => input (F.out (workLength coins word.length)))
    _=avg (fun coin : Bits (coins.eval word.length) => acceptProb F (List.ofFn coin++word)) := by
      apply congrArg avg
      funext coin
      exact branchOutput_probability coins F word coin

end Integration9_9.RandomizedCircuit

end

end P2MDyadicModule103

/- Helper module Solutions.AdvantageBridgeRankOneCallsOnce. -/
section P2MDyadicModule104

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.RandomizedCircuit

open InfoLossLAR.WorstCase

open Integration9_9.LARCoinLayout Integration9_9.LARRankOneMachine Integration9_9.TM2PlatformSerialization

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem passOutput_poly : Poly passOutput := by
  unfold passOutput
  fun_prop

theorem passOutput_polyTime : PolyTimeComputable passOutput := polyTime_of_poly passOutput_poly

theorem passOutput_append (word : Str) (bit : Bool) : passOutput (word++[bit])=[bit] := by
  simp [passOutput,List.reverse_append]

end Integration9_9.RandomizedCircuit

end P2MDyadicModule104

/- Helper module Solutions.AdvantageBridgeNativeCallsOnce. -/
section P2MDyadicModule105

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBodySemantics

open InfoLossLAR.WorstCase

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary

open Integration9_9.RandomizedCircuit

theorem genericBody_preservesClassicalInput (R : QuerySpecification) (D : Family) :
    PreservesClassicalInput (GenericBody.bodyFamily R.machine D) := by
  intro word output hn index
  exact bodyFamily_input_support R D word output hn index

/-- A genuine native preprocessor and the original IsQPT D suffice for the
complete actual uniformly generated quantum family, with no added Uniform premise. -/
theorem nativeFamily_isQPT {pre : Str → Str} (P : PolyProgram id id pre) (coins : Polynomial ℕ)
    (D : Family) (hD : IsQPT D) : IsQPT (nativeFamily P coins D) :=
  RandomizedCircuit.family_isQPT coins _
    (GenericBody.bodyFamily_isQPT (specificationOfPre P coins).machine D hD)

/-- Exact platform input and acceptance semantics of the complete actual
quantum implementation, for every raw word and every native polynomial pre. -/
theorem nativeFamily_acceptProb {pre : Str → Str} (P : PolyProgram id id pre) (coins : Polynomial ℕ)
    (D : Family) (word : Str) :
    acceptProb (nativeFamily P coins D) word=
      avg (fun coin : Bits (coins.eval word.length) => acceptProb D (pre (encPair (List.ofFn coin) word))) := by
  unfold nativeFamily
  rw [RandomizedCircuit.family_acceptProb coins _
    (genericBody_preservesClassicalInput (specificationOfPre P coins) D) word]
  apply congrArg avg
  funext coin
  rw [bodyFamily_actual_acceptProb (specificationOfPre P coins) D]
  exact congrArg (acceptProb D) (specificationOfPre_query P coins (List.ofFn coin) word (by simp))

/-- The complete actual quantum implementation meets the platform's literal
single classical-prepared D-call definition, with true raw TM2 pre and post. -/
theorem nativeFamily_callsOnce {pre : Str → Str} (P : PolyProgram id id pre) (coins : Polynomial ℕ)
    (D : Family) : CallsOnce (nativeFamily P coins D) D := by
  refine ⟨pre,passOutput,coins,⟨P.stock⟩,passOutput_polyTime,?_⟩
  intro word
  rw [nativeFamily_acceptProb]
  apply congrArg avg
  funext coin
  simp [passOutput_append]

/-- Fully constructive one-call quantum wrapper for a genuine native classical
polynomial preprocessor. All gate descriptions and resource bounds are proved. -/
theorem exists_native_one_call {pre : Str → Str} (P : PolyProgram id id pre) (coins : Polynomial ℕ)
    (D : Family) (hD : IsQPT D) :
    ∃ B : Family,IsQPT B ∧ CallsOnce B D ∧
      ∀ word,acceptProb B word=avg (fun coin : Bits (coins.eval word.length) =>
        acceptProb D (pre (encPair (List.ofFn coin) word))) :=
  ⟨nativeFamily P coins D,nativeFamily_isQPT P coins D hD,nativeFamily_callsOnce P coins D,
    nativeFamily_acceptProb P coins D⟩

end Integration9_9.GenericBodySemantics

end

end P2MDyadicModule105

/- Helper module Solutions.AdvantageBridgeAffineActualProbability. -/
section P2MDyadicModule106

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity AFT

open scoped BigOperators Classical

private theorem actual_uniform_expectation {α : Type} [Fintype α] [Nonempty α] (test : α → ℝ) :
    (FiniteDist.uniform α).expectation test=avg test := by
  simp only [FiniteDist.expectation,FiniteDist.uniform_weight,avg,←Finset.mul_sum]
  ring

/-- Exact observed-table presentation of platform real LWE, retaining its one
shared secret and independently sampled errors. -/
theorem prRealLWE_eq_observedTable {q d N : ℕ} [NeZero q] (B : Family) (lam : ℕ) (pp : Str) (t : ℕ)
    (source : FiniteDist (Fin d → ZMod q)) :
    prRealLWE B lam pp q N d t source.weight=
      avg (fun secret : Fin N → ZMod q =>
        (larObservedRealTableLaw q N d t source secret).expectation
          (fun table => acceptProb B (encInput lam pp (encTable table)))) := by
  unfold prRealLWE
  apply congrArg avg
  funext secret
  rw [larObservedRealTableLaw,FiniteDist.expectation_map,FiniteDist.expectation_prod,actual_uniform_expectation]
  rfl

theorem prIdealLWE_eq_observedTable {q d N : ℕ} [NeZero q] (B : Family) (lam : ℕ) (pp : Str) (t : ℕ) :
    prIdealLWE B lam pp q N d t=
      (larObservedIdealTableLaw q N d t).expectation
        (fun table => acceptProb B (encInput lam pp (encTable table))) := by
  unfold prIdealLWE
  rw [larObservedIdealTableLaw,FiniteDist.expectation_map,FiniteDist.expectation_prod]
  simp only [actual_uniform_expectation,Function.comp_def]

end InfoLossLAR.WorstCase

end

end P2MDyadicModule106

/- Helper module AverageLaw. -/
section P2MDyadicModule107

set_option autoImplicit false

set_option maxHeartbeats 800000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GeneralRankComparison

open QAlgorithms.Complexity AFT

open scoped Classical BigOperators

private theorem expect_close {α : Type} [Fintype α] (μ : FiniteDist α)
    (f g : α → ℝ) (δ : ℝ) (h : ∀ x, |f x-g x| ≤ δ) :
    |μ.expectation f - μ.expectation g| ≤ δ := by
  rw [←FiniteDist.expectation_sub]
  have hi : μ.expectation (fun x => f x-g x) ≤ μ.expectation (fun _=>δ) := by
    unfold FiniteDist.expectation
    exact Finset.sum_le_sum fun x _=>mul_le_mul_of_nonneg_left (abs_le.mp (h x)).2 (μ.nonneg x)
  have lo : μ.expectation (fun _=> -δ) ≤ μ.expectation (fun x => f x-g x) := by
    unfold FiniteDist.expectation
    exact Finset.sum_le_sum fun x _=>mul_le_mul_of_nonneg_left (abs_le.mp (h x)).1 (μ.nonneg x)
  rw [FiniteDist.expectation_const] at hi lo
  exact abs_le.mpr ⟨lo,hi⟩

private theorem avg_eq {α : Type} [Fintype α] [Nonempty α] (f : α → ℝ) :
    avg f=(FiniteDist.uniform α).expectation f := by
  simp only [FiniteDist.expectation,FiniteDist.uniform_weight,avg,←Finset.mul_sum]
  ring

theorem rankOne_error (B D : Family) (lam : ℕ) (pp : Str) (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (source : FiniteDist (Fin d → ZMod q)) (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q))
    (δ : ℝ)
    (hk : ∀ table : Fin t → Matrix (Fin d) (Fin N) (ZMod q) × (Fin d → ZMod q),
      |acceptProb B (encInput lam pp (encTable table)) -
        avg (fun aux : Fin N→ZMod q=> avg (fun marks : Fin t → Fin ℓ → ZMod q =>
          acceptProb D (rankOneEncodedQuery lam pp q N d ℓ t direction (aux,marks) table)))| ≤ δ) :
    |advLWE B lam pp q N d t source.weight -
        abs (prRankOneRealLAR D lam pp q N d ℓ t source direction -
         prRankOneIdealLAR D lam pp q N d ℓ t direction)| ≤ 2*δ := by
  have hr : |prRealLWE B lam pp q N d t source.weight -
      prRankOneRealLAR D lam pp q N d ℓ t source direction| ≤ δ := by
    rw [prRealLWE_eq_observedTable,←larObservedRealTableLaw_rankOne,
      avg_eq (fun secret => (larObservedRealTableLaw _ _ _ _ _ secret).expectation _),
      avg_eq (fun secret => (larObservedRealTableLaw _ _ _ _ _ secret).expectation _)]
    exact expect_close _ _ _ _ (fun secret=>expect_close _ _ _ _ hk)
  have hi : |prIdealLWE B lam pp q N d t -
      prRankOneIdealLAR D lam pp q N d ℓ t direction| ≤ δ := by
    rw [prIdealLWE_eq_observedTable,←larObservedIdealTableLaw_rankOne]
    exact expect_close _ _ _ _ hk
  unfold advLWE
  exact (abs_abs_sub_abs_le _ _).trans (by
    rw [show prRealLWE B lam pp q N d t source.weight-prIdealLWE B lam pp q N d t -
        (prRankOneRealLAR D lam pp q N d ℓ t source direction - prRankOneIdealLAR D lam pp q N d ℓ t direction)=
        (prRealLWE B lam pp q N d t source.weight - prRankOneRealLAR D lam pp q N d ℓ t source direction) -
        (prIdealLWE B lam pp q N d t - prRankOneIdealLAR D lam pp q N d ℓ t direction) by ring]
    exact (abs_sub _ _).trans (by linarith))

end InfoLossLAR.WorstCase.GeneralRankComparison

end P2MDyadicModule107

/- Helper module TicketLaw. -/
section P2MDyadicModule108

set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace InfoLossLAR.WorstCase.GeneralRank

open scoped BigOperators Classical

def ticketBits (count : ℕ) := 3*Nat.size count+2

private theorem residue_blocks (c : ℕ) (hc : 0<c) (g : Fin c → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n*c), g ⟨i%c,Nat.mod_lt _ hc⟩ =
       (n:ℝ) * ∑ i : Fin c, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add,ih,Nat.cast_succ,add_mul,one_mul]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun i => g ⟨(n*c+i)%c,Nat.mod_lt _ hc⟩) c]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Fin.ext
    simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

theorem mod_average {c K : ℕ} (hc : 0<c) (hK : 0<K) (g : Fin c → ℝ)
    (hb : ∀ i, g i ∈ Set.Icc 0 1) :
    |avg (fun i : Fin K => g ⟨i.val%c,Nat.mod_lt _ hc⟩) - avg g| ≤ (c:ℝ)/K := by
  letI : Nonempty (Fin c) := ⟨⟨0,hc⟩⟩
  let f (i : ℕ) : ℝ := g ⟨i%c,Nat.mod_lt _ hc⟩
  let t := ∑ i ∈ Finset.range (K%c), f (K/c*c+i)
  have ht0 : 0 ≤ t := Finset.sum_nonneg (fun i _ => (hb _).1)
  have ht1 : t ≤ ((K%c:ℕ):ℝ) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (K%c), (1:ℝ) := Finset.sum_le_sum (fun i _ => (hb _).2)
      _ = _ := by simp
  let a := avg g
  have hmean : a ∈ Set.Icc 0 1 := avg_mem_unitInterval _ hb
  have hdecomp : (K/c)*c+K%c=K := Nat.div_add_mod' K c
  have hsum : (∑ i : Fin K, f i) = (K/c:ℕ) * (∑ i, g i) + t := by
    rw [Fin.sum_univ_eq_sum_range f K]
    conv_lhs => rw [← hdecomp,Finset.sum_range_add]
    rw [show (∑ i ∈ Finset.range ((K/c)*c),f i) = _ from residue_blocks c hc g (K/c)]
  have hc' : (0:ℝ)<c := by exact_mod_cast hc
  have hK' : (0:ℝ)<K := by exact_mod_cast hK
  have hcard : (∑ i, g i) = (c:ℝ)*a := by
    dsimp [a,avg]
    rw [Fintype.card_fin]
    field_simp
  have hk' : ((K/c:ℕ):ℝ)*(c:ℝ) + ((K%c:ℕ):ℝ) = (K:ℝ) := by exact_mod_cast hdecomp
  have hnum : avg (fun i : Fin K => f i) - a = (t-((K%c:ℕ):ℝ)*a)/K := by
    change (∑ i : Fin K,f i)/(Fintype.card (Fin K):ℝ)-a=_
    rw [Fintype.card_fin,hsum,hcard]
    field_simp
    nlinarith only [congrArg (fun b : ℝ => b*a) hk']
  have hr : ((K%c:ℕ):ℝ) ≤ c := by exact_mod_cast (Nat.mod_lt K hc).le
  have ha : 0 ≤ ((K%c:ℕ):ℝ)*a := mul_nonneg (Nat.cast_nonneg _) hmean.1
  have ha' : ((K%c:ℕ):ℝ)*a ≤ ((K%c:ℕ):ℝ) :=
    mul_le_of_le_one_right (Nat.cast_nonneg _) hmean.2
  change |avg (fun i : Fin K => f i) - a| ≤ _
  rw [hnum,abs_div,abs_of_pos hK']
  exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith,by linarith⟩) hK'.le

theorem bit_budget_error {q c : ℕ} (hq : 0<q) (hqc : q≤c) :
    (2:ℝ)*q*((c:ℝ)/(2:ℝ)^ticketBits c) ≤ (c:ℝ)⁻¹ := by
  have hc : (0:ℝ)<c := by exact_mod_cast (hq.trans_le hqc)
  have hsize : (c:ℝ) ≤ (2:ℝ)^Nat.size c := by exact_mod_cast (Nat.lt_size_self c).le
  have hq' : (q:ℝ) ≤ c := by exact_mod_cast hqc
  have hpower : (2:ℝ)^ticketBits c = ((2:ℝ)^Nat.size c)^3*4 := by
    rw [ticketBits,pow_add, Nat.mul_comm 3, pow_mul]; norm_num
  have hcub := pow_le_pow_left₀ hc.le hsize 3
  have hmul := mul_le_mul_of_nonneg_right hq' (sq_nonneg (c:ℝ))
  rw [hpower, ← one_div]
  field_simp
  nlinarith only [hcub,hmul,le_of_lt (pow_pos hc 3)]

end InfoLossLAR.WorstCase.GeneralRank

end P2MDyadicModule108

/- Helper module Solutions.AdvantageBridgeNativeBlockAverage. -/
section P2MDyadicModule109

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBodySemantics

open InfoLossLAR.WorstCase QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

/-- The average on two independent finite sources is its exact nested average. -/
theorem avg_product {First Second : Type} [Fintype First] [Fintype Second]
    (test : First × Second → ℝ) : avg test=avg (fun first => avg (fun second => test (first,second))) := by
  simp only [avg,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,←Finset.sum_div]
  ring

end Integration9_9.GenericBodySemantics

end

end P2MDyadicModule109

/- Helper module CoinPrep. -/
section P2MDyadicModule110

set_option autoImplicit false

set_option maxRecDepth 15000

set_option maxHeartbeats 1500000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GeneralRank

open QMCNumericRuntime Integration9_9 LARPlatformEncoding LARCoinMachine OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic QAlgorithms.Complexity

open scoped BigOperators Classical

def ticketCount (modulus : Str → ℕ) (slots : Str → List Unit) (w : Str) :=
  powerWithSlots (modulus w, slots w)

def preprocess (modulus : Str → ℕ) (slots : Str → List Unit) (render : Str × List ℕ → Str)
    (input : Str) : Str :=
  let parts := readS input
  let w := (readS parts.1).2
  let c := ticketCount modulus slots w
  let v := bitValue (parts.2.take (ticketBits c))
  render (w,decodeBaseQ (modulus w,slots w,v%c))

theorem count_poly {m : Str → ℕ} {s : Str → List Unit} (hm : Poly m) (hs : Poly s) :
    Poly (ticketCount m s) := by
  unfold ticketCount
  exact Poly.comp powerWithSlots_poly (Poly.pair hm hs)

theorem preprocess_poly {m : Str → ℕ} {s : Str → List Unit} {r : Str × List ℕ → Str}
    (hm : Poly m) (hs : Poly s) (hr : Poly r) : Poly (preprocess m s r) := by
  have hcount := count_poly hm hs
  have hbits : Poly ticketBits := by unfold ticketBits; fun_prop
  let word (v : Str) := (readS (readS v).1).2
  let coins (v : Str) := (readS v).2
  have hw : Poly word := by unfold word; fun_prop
  have ht : Poly coins := by unfold coins; fun_prop
  have htake : Poly (fun x => (coins x).take (ticketBits (ticketCount m s (word x)))) :=
    Poly.comp parser_take_poly (Poly.pair ht (Poly.comp hbits (Poly.comp hcount hw)))
  have hval := Poly.comp bitValue_poly htake
  have hticket := Poly.comp naturalModulus_poly (Poly.pair hval (Poly.comp hcount hw))
  exact Poly.comp (f:=r) (g:=fun x => (word x, decodeBaseQ (m (word x),s (word x),
    bitValue ((coins x).take (ticketBits (ticketCount m s (word x)))) % ticketCount m s (word x)))) hr (Poly.pair hw (Poly.comp (f:=decodeBaseQ) decodeBaseQ_poly
    (Poly.pair (Poly.comp hm hw) (Poly.pair (Poly.comp hs hw) hticket))))

theorem budget {m : Str → ℕ} {s : Str → List Unit} (hm : Poly m) (hs : Poly s) :
    ∃ p : Polynomial ℕ, ∀ w, ticketBits (ticketCount m s w) ≤ p.eval w.length := by
  let P := (count_poly hm hs).program
  refine ⟨3*(P.sizeBound.comp (3*Polynomial.X))+2,?_⟩
  intro w
  have h := P.length_bound w
  change (Nat.bits (ticketCount m s w)).length ≤ P.sizeBound.eval (encodeList encodeBool w).length at h
  simp only [BooleanLists.length,Nat.size_eq_bits_len] at h
  simp only [ticketBits,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_comp,Polynomial.eval_X]
  omega

private theorem take_bits {k l : ℕ} (h : k≤l) (b : Fin l → Bool) :
    (List.ofFn b).take k=List.ofFn (fun i : Fin k => b (Fin.castLE h i)) := by
  apply List.ext_getElem <;> simp [Nat.min_eq_left h,List.getElem_take]

private theorem read_end (w : Str) : (readS (encS w)).2=w := by
  simpa using congrArg Prod.snd (readS_append w [])

theorem machine (m : Str → ℕ) (s : Str → List Unit) (r : Str × List ℕ → Str)
    (hm : Poly m) (hs : Poly s) (hr : Poly r) (D : Family) (hD : IsQPT D) :
    ∃ B : Family, IsQPT B ∧ CallsOnce B D ∧ ∀ w : Str, ∀ hc : 0 < ticketCount m s w,
      |acceptProb B w - avg (fun j : Fin (ticketCount m s w) =>
         acceptProb D (r (w,decodeBaseQ (m w,s w,j.val))))| ≤
        (ticketCount m s w:ℝ) / (2:ℝ)^ticketBits (ticketCount m s w) := by
  classical
  obtain ⟨p,hp⟩ := budget hm hs
  let P := LARCoinLayout.rawPolyProgram (preprocess_poly hm hs hr)
  obtain ⟨B,hB,hone,hlaw⟩ := GenericBodySemantics.exists_native_one_call P p D hD
  refine ⟨B,hB,hone,?_⟩
  intro w hc
  let c := ticketCount m s w
  let k := ticketBits c
  let g (j : Fin c) := acceptProb D (r (w,decodeBaseQ (m w,s w,j.val)))
  let raw (b : Fin k → Bool) : ℝ := g ⟨(boundedBoolTicket k b).val%c, Nat.mod_lt _ hc⟩
  have hprefix : k ≤ p.eval w.length := hp w
  have hval (b : Fin (p.eval w.length) → Bool) : acceptProb D
      (preprocess m s r (encPair (List.ofFn b) w)) = raw (fun i => b (i.castLE hprefix)) := by
    simp only [preprocess,encPair,readS_append,read_end]
    rw [take_bits hprefix,bitValue_boundedBoolTicket]
  have hB' : acceptProb B w = avg raw := by
    rw [hlaw]
    change avg (fun b => acceptProb D (preprocess m s r (encPair (List.ofFn b) w)))=_
    simp_rw [hval]
    exact FairBitPadding.avg_prefix hprefix raw
  have he := FairBitPadding.avg_equiv (boundedBoolTicket k)
    (fun i : Fin (2^k) => g ⟨i.val%c,Nat.mod_lt _ hc⟩)
  change avg raw = _ at he
  rw [hB',he]
  exact_mod_cast mod_average hc (by positivity : 0<2^k) g (fun j => acceptProb_mem_unitInterval D _)

end InfoLossLAR.WorstCase.GeneralRank

end P2MDyadicModule110

/- Helper module DigitLaw. -/
section P2MDyadicModule111

set_option autoImplicit false

set_option maxHeartbeats 900000

namespace InfoLossLAR.WorstCase.GeneralRank

open Integration9_9 LARCoinMachine

open scoped BigOperators Classical

def joinDigits {q N t ℓ : ℕ} (aux : Fin N → ZMod q) (marks : Fin t → Fin ℓ → ZMod q) :
    List ℕ := List.ofFn (fun j => ((Fin.append aux (fun k : Fin (t*ℓ) =>
      marks (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) j).val)

private theorem reassemble {q N t ℓ : ℕ} (v : Fin (N+t*ℓ) → ZMod q) :
    joinDigits (boundedSplit (ZMod q) N t ℓ v).1 (boundedSplit (ZMod q) N t ℓ v).2 =
      List.ofFn (fun i => (v i).val) := by
  unfold joinDigits
  apply congrArg List.ofFn
  funext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp only [Fin.append_left,boundedSplit]
  · simp only [Fin.append_right,boundedSplit,Prod.mk.eta,Equiv.apply_symm_apply]

theorem digit_average (q N t ℓ : ℕ) [NeZero q] (slots : List Unit) (h : slots.length=N+t*ℓ)
    (test : List ℕ → ℝ) :
    avg (fun j : Fin (q^(N+t*ℓ)) => test (decodeBaseQ (q,slots,j.val))) =
    avg (fun aux : Fin N → ZMod q => avg (fun marks : Fin t → Fin ℓ → ZMod q =>
      test (joinDigits aux marks))) := by
  let f := fun a : (Fin N → ZMod q) × (Fin t → Fin ℓ → ZMod q) => test (joinDigits a.1 a.2)
  have hj (j : Fin (q^(N+t*ℓ))) : test (decodeBaseQ (q,slots,j.val)) = f (boundedJointEquiv q N t ℓ j) := by
    let y := boundedFieldDecode q (N+t*ℓ) j
    have hjoint : boundedJointEquiv q N t ℓ j = boundedSplit (ZMod q) N t ℓ y := by
      rw [boundedSplit_eq,show y = boundedFieldEquiv q (N+t*ℓ) j from boundedFieldDecode_eq _ _ _]
      rfl
    rw [hjoint]
    dsimp only [f]
    rw [reassemble,decodeBaseQ_eq q _ _ slots h]
    congr 1
    apply congrArg List.ofFn
    funext i
    exact (boundedFieldDecode_val _ _ _ i).symm
  simp_rw [hj]
  rw [FairBitPadding.avg_equiv (boundedJointEquiv q N t ℓ) f, GenericBodySemantics.avg_product]

end InfoLossLAR.WorstCase.GeneralRank

end P2MDyadicModule111

/- Helper module Integration9_9.TM2NativeAffineApply. -/
section P2MDyadicModule112

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option maxRecDepth 10000

set_option synthInstance.maxSize 1024

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.TM2NativeAffineApply

open AFT AFT.BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open InfoLossLAR.WorstCase

open scoped BigOperators

private theorem zip_ofFn {α β : Type} {n : ℕ} (f : Fin n→α) (g : Fin n→β) :
    (List.ofFn f).zip (List.ofFn g)=List.ofFn (fun i=>(f i,g i)) := by apply List.ext_getElem <;> simp

theorem dot_ofFn {n : ℕ} (f g : Fin n→ℤ) : dot (List.ofFn f,List.ofFn g)=∑i,f i*g i := by
  simp only [dot,zip_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn]

theorem residue_value (q : ℕ) [NeZero q] (z : ℤ) : TM2NativeBodyKernel.emodNatural (z,q)=(z : ZMod q).val := by
  rw [TM2NativeBodyKernel.emodNatural_eq]
  have h := ZMod.val_intCast (n:=q) z
  simpa only [Int.toNat_natCast] using (congrArg Int.toNat h).symm

end Integration9_9.TM2NativeAffineApply

end P2MDyadicModule112

/- Helper module NativeRank. -/
section P2MDyadicModule113

set_option autoImplicit false

set_option maxHeartbeats 500000

set_option maxRecDepth 15000

set_option backward.isDefEq.respectTransparency true

namespace InfoLossLAR.WorstCase.GenericRank

open QAlgorithms.Complexity Integration9_9 Integration9_9.LARPlatformEncoding

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime

open scoped BigOperators Classical

abbrev Sample := TM2NativeAffineApply.Sample

abbrev NativeV := List (List ℤ)

def readV (s : Str) : NativeV :=
  let rest := (readParameters s).1
  let t := TM2NativeAffineEncoding.readMatrix rest
  let u := TM2NativeAffineEncoding.readMatrix t.1
  (TM2NativeAffineEncoding.readMatrix u.1).2

@[fun_prop] theorem readV_poly : Poly readV := by unfold readV; fun_prop

def rField (s : Str) : ℕ := (readParameters s).2.2.2.2

@[fun_prop] theorem rField_poly : Poly rField := by unfold rField; fun_prop

def obs (s : Str) := (readObservedInput s).2

@[fun_prop] theorem obs_poly : Poly obs := by unfold obs; fun_prop

def modulus (s : Str) : ℕ := (readParameters (obs s).2.1).2.1

@[fun_prop] theorem modulus_poly : Poly modulus := by unfold modulus; fun_prop

section Machine

attribute [local irreducible] readV rField obs modulus readParameters readObservedInput

def labelSlots (s : Str) : List Unit := ((readV s).drop (rField s)).map fun _ => ()

@[fun_prop] theorem labelSlots_poly : Poly labelSlots := by
  have hd : Poly (fun s : Str => (readV s).drop (rField s)) :=
    Poly.comp (f:=fun p : NativeV × ℕ => p.1.drop p.2) (g:=fun s : Str => (readV s,rField s)) parser_drop_poly (Poly.pair readV_poly rField_poly)
  exact Poly.list_map (f := fun (_ : Str) (_ : List ℤ) => ()) (by fun_prop) hd

attribute [local irreducible] labelSlots

def slots (s : Str) : List Unit :=
  LARRankOneMachine.observedAuxiliarySlots (obs s).2.2 ++
    ((obs s).2.2.flatMap fun _ => labelSlots (obs s).2.1)

@[fun_prop] theorem slots_poly : Poly slots := by
  have htab : Poly (fun s : Str => (obs s).2.2) := by fun_prop
  have hlist := Poly.list_flatMap (f := fun (s : Str) (_ : Sample) => labelSlots (obs s).2.1)
    (as := fun s => (obs s).2.2) (by fun_prop) htab
  exact Poly.comp (f := fun p : List Unit × List Unit => p.1 ++ p.2)
    (g := fun s : Str => (LARRankOneMachine.observedAuxiliarySlots (obs s).2.2,
        (obs s).2.2.flatMap fun _ => labelSlots (obs s).2.1))
    Poly.list_append (Poly.pair (by fun_prop) hlist)

def idxN (l : List ℕ) : List ℕ := List.range l.length

def idxR (l : List (List ℕ)) : List ℕ := List.range l.length

def idxS (l : List Sample) : List ℕ := List.range l.length

def idxU (l : List Unit) : List ℕ := List.range l.length

@[fun_prop] theorem idxN_poly : Poly idxN := Poly.list_indices

@[fun_prop] theorem idxR_poly : Poly idxR := Poly.list_indices

@[fun_prop] theorem idxS_poly : Poly idxS := Poly.list_indices

@[fun_prop] theorem idxU_poly : Poly idxU := Poly.list_indices

def mark (p : (Str × List ℕ) × ℕ) : List ℕ :=
  let pp := (obs p.1.1).2.1
  let n := (readParameters pp).2.2.1
  let l := labelSlots pp
  (idxU l).map fun j => (p.1.2[n+p.2*l.length+j]?).getD 0

@[fun_prop] theorem mark_poly : Poly mark := by unfold mark; fun_prop

def wts (p : (Str × ℕ) × List ℕ) : List ℤ :=
  let row := ((readV p.1.1)[p.1.2]?).getD []
  (idxN p.2).map fun j => (row[rField p.1.1+j]?).getD 0

@[fun_prop] theorem wts_poly : Poly wts := by unfold wts; fun_prop

attribute [local irreducible] wts mark

abbrev Args := (Str × List ℕ) × (ℕ × (Sample × List ℕ))

def entry (p : Args × (ℕ × ℕ)) : ℕ :=
  let x := p.1
  let i := p.2.1
  let j := p.2.2
  let a := (((x.2.2.1.1[i]?).getD [])[j]?).getD 0
  let b := (x.2.2.1.2[i]?).getD 0
  let u := (x.1.2[j]?).getD 0
  let shift := TM2NativeAffineApply.dot (wts ((x.1.1,i),x.2.2.2),x.2.2.2.map fun (m : ℕ) => (m:ℤ))
  TM2NativeBodyKernel.emodNatural (-(a:ℤ) + ((b:ℤ)+shift)*(u:ℤ), x.2.1)

@[fun_prop] theorem entry_poly : Poly entry := by unfold entry; fun_prop

def sample (x : Args) : Sample :=
  ((idxR x.2.2.1.1).map (fun i =>
    (idxN ((x.2.2.1.1[i]?).getD [])).map (fun j => entry (x,(i,j)))),x.2.2.2)

@[fun_prop] theorem sample_poly : Poly sample := by
  have e : Poly (fun p : (Args × ℕ) × ℕ => entry (p.1.1,(p.1.2,p.2))) := by fun_prop
  have row : Poly (fun p : Args × ℕ => (idxN ((p.1.2.2.1.1[p.2]?).getD [])).map
    (fun j => entry (p.1,(p.2,j)))) := Poly.list_map e (by fun_prop)
  unfold sample
  exact Poly.pair (Poly.list_map row (by fun_prop)) (by fun_prop)

def applyDigits (p : Str × List ℕ) : Str :=
  let o := obs p.1
  serializeObservedInput (o.1,o.2.1,(idxS o.2.2).map fun i =>
    sample ((o.2.1,p.2),modulus p.1,(o.2.2[i]?).getD ([],[]),mark (p,i)))

@[fun_prop] theorem applyDigits_poly : Poly applyDigits := by unfold applyDigits; fun_prop

end Machine

abbrev Tables (F : RoundingFamily) (n t : ℕ) := Fin t →
    Matrix (Fin (F.d n)) (Fin (F.N n)) (ZMod (F.q n)) × (Fin (F.d n) → ZMod (F.q n))

private def rawSample {q d N : ℕ} (A : Matrix (Fin d) (Fin N) (ZMod q)) (b : Fin d → ZMod q) : Sample :=
  (List.ofFn (fun i => List.ofFn (fun j => (A i j).val)),List.ofFn (fun i => (b i).val))

private theorem obs_exact (F : RoundingFamily) (n t : ℕ) (table : Tables F n t) :
    obs (encInput n (F.pp n) (encTable table)) =
    (unary n,F.pp n,List.ofFn fun i => rawSample (table i).1 (table i).2) := by
  have h := readObservedInput_append n (F.pp n) [] table
  simp only [List.append_nil] at h
  exact congrArg Prod.snd h

private theorem pp_exact (F : RoundingFamily) (n : ℕ) :
    readParameters (F.pp n) = (encMat encI (F.T n) ++ encMat encI (F.smith n).U ++
      encMat encI (F.smith n).V ++ encQ (F.σ n),F.q n,F.N n,F.d n,F.r n) := by
  simp [readParameters,RoundingFamily.pp,List.append_assoc,readB_append]

private theorem V_exact (F : RoundingFamily) (n : ℕ) :
    readV (F.pp n) = List.ofFn (fun i => List.ofFn ((F.smith n).V i)) := by
  simp [readV,pp_exact,List.append_assoc,TM2NativeAffineEncoding.readMatrix_append]

private theorem label_len (F : RoundingFamily) (n : ℕ) :
    (labelSlots (F.pp n)).length = F.ell n := by
  simp [labelSlots,rField,pp_exact,V_exact,RoundingFamily.ell]

theorem modulus_exact (F : RoundingFamily) (n t : ℕ) (_ht : 0<t) (table : Tables F n t) :
    modulus (encInput n (F.pp n) (encTable table)) = F.q n := by
  simp [modulus,obs_exact,pp_exact]

theorem slots_length (F : RoundingFamily) (n t : ℕ) (ht : 0<t) (table : Tables F n t) :
    (slots (encInput n (F.pp n) (encTable table))).length = F.N n+t*F.ell n := by
  have hd : 0 < F.d n := lt_of_le_of_lt (Nat.zero_le _) (F.ell_pos n)
  simp [slots,obs_exact,LARRankOneMachine.observedAuxiliarySlots,rawSample,List.head?_eq_getElem?,
    ht,hd,List.length_flatMap,label_len,List.sum_ofFn]

private theorem J_entry (F : RoundingFamily) (n : ℕ) (i : Fin (F.d n)) (j : Fin (F.ell n)) :
    (F.smith n).J i j = ((F.smith n).V i ⟨F.r n+j.val,by
      have ht:=j.isLt; have hr:=F.ell_pos n; unfold RoundingFamily.ell at ht; omega⟩ : ℤ) := by
  let k : Fin (F.d n) := ⟨F.r n+j.val,by
    have ht:=j.isLt; have hr:=F.ell_pos n; unfold RoundingFamily.ell at ht; omega⟩
  have h (k' : Fin (F.d n)) : embE (F.r n) (F.d n) k' j = if k'=k then 1 else 0 := by
    simp [embE,k,Fin.ext_iff]
  change ((∑ k', (F.smith n).V i k' * embE (F.r n) (F.d n) k' j : ℤ) : ZMod (F.q n)) = _
  simp [h,mul_ite,k]

private theorem idxEq {α β : Type} {n : ℕ} (f : Fin n → α) (g : ℕ → β) :
    (List.range (List.ofFn f).length).map g = List.ofFn (fun i : Fin n => g i.val) := by
  apply List.ext_getElem <;> simp

private theorem shift_exact (F : RoundingFamily) (n : ℕ) (i : Fin (F.d n)) (m : Fin (F.ell n) → ZMod (F.q n)) :
    (TM2NativeAffineApply.dot (wts ((F.pp n,i.val),List.ofFn fun j => (m j).val),
      (List.ofFn fun j => (m j).val).map (fun (x : ℕ) => (x:ℤ))) : ZMod (F.q n)) =
      (F.smith n).J.mulVec m i := by
  let v (j : Fin (F.ell n)) : Fin (F.d n) := ⟨F.r n+j.val,by
    have ht:=j.isLt; have hr:=F.ell_pos n; unfold RoundingFamily.ell at ht; omega⟩
  have hw : wts ((F.pp n,i.val),List.ofFn fun j => (m j).val) =
      List.ofFn (fun j => (F.smith n).V i (v j)) := by
    simp only [wts,V_exact,rField,pp_exact,List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some,idxN,idxEq]
    apply congrArg List.ofFn; funext j
    have hk := (v j).isLt
    simp [v] at hk ⊢
    rw [dif_pos hk]; rfl
  rw [hw,List.map_ofFn,TM2NativeAffineApply.dot_ofFn]
  simp only [Int.cast_sum,Int.cast_mul,Function.comp_apply,Int.cast_natCast,ZMod.natCast_zmod_val,
    Matrix.mulVec,dotProduct,v]
  apply Finset.sum_congr rfl; intro j _
  rw [J_entry F n i j]

def joined {q N t ℓ : ℕ} (aux : Fin N → ZMod q) (ms : Fin t → Fin ℓ → ZMod q) : Fin (N + t*ℓ) → ZMod q :=
  Fin.append aux (fun k => ms (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

private theorem digitAt {q N t ℓ : ℕ} (a : Fin N → ZMod q) (m : Fin t → Fin ℓ → ZMod q)
    (i : Fin (N+t*ℓ)) :
    ((List.ofFn (fun k => (joined a m k).val))[i.val]?).getD 0 = (joined a m i).val := by simp

private theorem digitAux {q N t ℓ : ℕ} (a : Fin N → ZMod q) (m : Fin t → Fin ℓ → ZMod q)
    (i : Fin N) :
    ((List.ofFn (fun k => (joined a m k).val))[i.val]?).getD 0 = (a i).val := by
  simpa [joined,Fin.append_left] using digitAt a m (i.castAdd (t*ℓ))

private theorem digitMark {q N t ℓ : ℕ} (a : Fin N → ZMod q) (m : Fin t → Fin ℓ → ZMod q)
    (i : Fin t) (j : Fin ℓ) :
    ((List.ofFn (fun k => (joined a m k).val))[N+i.val*ℓ+j.val]?).getD 0 = (m i j).val := by
  have h := digitAt a m (Fin.natAdd N (finProdFinEquiv (i,j)))
  rw [show joined a m (Fin.natAdd N (finProdFinEquiv (i,j)))=m i j by
    unfold joined
    rw [Fin.append_right,Equiv.symm_apply_apply]] at h
  convert h using 3
  simp only [Fin.val_natAdd,finProdFinEquiv_apply_val]
  ring

private theorem mark_exact (F : RoundingFamily) (n t : ℕ) (table : Tables F n t)
    (aux : Fin (F.N n) → ZMod (F.q n)) (ms : Fin t → Fin (F.ell n) → ZMod (F.q n))
    (i : Fin t) :
    mark ((encInput n (F.pp n) (encTable table),List.ofFn fun k => (joined aux ms k).val),i.val) =
      List.ofFn (fun j => (ms i j).val) := by
  simp only [mark,obs_exact,pp_exact,idxU,label_len]
  have hr {α : Type} (k : ℕ) (f : ℕ → α) : (List.range k).map f = List.ofFn (fun j : Fin k => f j.val) := by
    apply List.ext_getElem <;> simp
  rw [hr]
  apply congrArg List.ofFn; funext j; exact digitMark aux ms i j

private theorem entry_exact (F : RoundingFamily) (n t : ℕ) (table : Tables F n t)
    (aux : Fin (F.N n) → ZMod (F.q n)) (ms : Fin t → Fin (F.ell n) → ZMod (F.q n))
    (k : Fin t) (i : Fin (F.d n)) (j : Fin (F.N n)) :
    entry (((F.pp n,List.ofFn fun k => (joined aux ms k).val),F.q n,
      rawSample (table k).1 (table k).2,List.ofFn fun j=>(ms k j).val),(i.val,j.val)) =
      ((larRankOnePreprocess aux (fun z => (F.smith n).J.mulVec z)
        (table k).1 (table k).2 (ms k)).1 i j).val := by
  unfold entry
  dsimp only
  rw [digitAux aux ms j]
  simp only [rawSample,List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some,
    TM2NativeAffineApply.residue_value]
  apply congrArg ZMod.val
  simp only [Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_natCast,ZMod.natCast_zmod_val,shift_exact,
    larRankOnePreprocess,Matrix.add_apply,Matrix.neg_apply,Matrix.vecMulVec_apply,Pi.add_apply]

theorem applyDigits_exact (F : RoundingFamily) (n t : ℕ) (ht : 0<t) (table : Tables F n t)
    (aux : Fin (F.N n) → ZMod (F.q n)) (ms : Fin t → Fin (F.ell n) → ZMod (F.q n)) :
    applyDigits (encInput n (F.pp n) (encTable table),List.ofFn (fun k => (joined aux ms k).val)) =
      rankOneEncodedQuery n (F.pp n) (F.q n) (F.N n) (F.d n) (F.ell n) t
        (fun u => (F.smith n).J.mulVec u) (aux,ms) table := by
  unfold applyDigits rankOneEncodedQuery
  rw [obs_exact,modulus_exact F n t ht table]
  dsimp only
  refine Eq.trans ?_ (serializeObservedInput_ofFn n (F.pp n) (fun i => larRankOnePreprocess aux
      (fun u => (F.smith n).J.mulVec u) (table i).1 (table i).2 (ms i)))
  apply congrArg serializeObservedInput
  apply congrArg (fun blocks : List Sample => (unary n,F.pp n,blocks))
  rw [idxS,idxEq]
  apply congrArg List.ofFn; funext k
  rw [mark_exact]
  simp only [List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some,sample,rawSample,idxN,idxR,idxEq]
  refine Prod.ext ?_ rfl
  apply congrArg List.ofFn; funext i
  apply congrArg List.ofFn; funext j
  exact entry_exact F n t table aux ms k i j

end InfoLossLAR.WorstCase.GenericRank

end P2MDyadicModule113

/- Helper module Reserve. -/
section P2MDyadicModule114

set_option autoImplicit false

open QAlgorithms.Complexity

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.GeneralRank

/-- A specified atom of the uniform label table agrees exactly with itself. -/
private theorem point_mean_gap {B : Type*} [Fintype B] [Nonempty B]
    (F : B → ℝ) (w : B) (hF : ∀ b, 0 ≤ F b ∧ F b ≤ 1) :
    |F w - avg F| ≤ 1 - (Fintype.card B : ℝ)⁻¹ := by
  classical
  have hcard : (0:ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hz (b : B) : |F w - F b| ≤ 1 := abs_le.mpr ⟨by linarith [(hF w).1,(hF b).2],by linarith [(hF w).2,(hF b).1]⟩
  have ht : |∑ b, (F w - F b)| ≤ (Fintype.card B : ℝ)-1 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ w)]
    simp only [sub_self,abs_zero,add_zero]
    calc
      _ ≤ ∑ _b ∈ Finset.univ.erase w, (1:ℝ) := Finset.sum_le_sum fun b _ => hz b
      _ = _ := by simp [Finset.card_erase_of_mem, Nat.cast_sub (show 1 ≤ Fintype.card B from Fintype.card_pos)]
  unfold avg
  rw [show F w - ((∑ b, F b) / (Fintype.card B : ℝ)) =
      (∑ b, (F w - F b)) / (Fintype.card B : ℝ) by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp]
  rw [abs_div,abs_of_pos hcard,div_le_iff₀ hcard]
  simpa [sub_mul, hcard.ne'] using ht

theorem zero_cost (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) (hzero : label 0=0) :
    |prRealLAR D lam pp q N d ℓ t label - prZeroSecretReplacedLAR D lam pp q N d ℓ t label|
      ≤ ((q : ℝ)^N)⁻¹ * (1 - ((q : ℝ)^(t*ℓ))⁻¹) := by
  rw [prRealLAR_zeroSecretReplacement_exact]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold larSecretAcceptance prIdealLAR
  apply avg_abs_sub_le
  intro M
  let f := fun labels : Fin t → Fin ℓ → ZMod q =>
    acceptProb D (encInput lam pp (encTable fun i => (M i,labels i)))
  have h := point_mean_gap f 0 (fun _ => acceptProb_mem_unitInterval D _)
  simpa [f,Matrix.mulVec_zero,hzero,Pi.zero_apply,Fintype.card_fun, ZMod.card, ← pow_mul, Nat.mul_comm] using h

theorem reserve (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) (hzero : label 0=0)
    (direction : (Fin ℓ → ZMod q) →+ (Fin d → ZMod q))
    (htranslate : ∀ input mark, label (input+direction mark)=label input+mark) :
    advLAR D lam pp q N d ℓ t label ≤
      (q : ℝ)*|prRankOneRealLAR D lam pp q N d ℓ t (larUniformZeroLaw label hzero) direction-
        prRankOneIdealLAR D lam pp q N d ℓ t direction|+
        ((q : ℝ)^N)⁻¹ * (1 - ((q : ℝ)^(t*ℓ))⁻¹) := by
  rw [prRankOneRealLAR_zero_eq D lam pp q N d ℓ t label hzero direction htranslate,prRankOneIdealLAR_eq]
  unfold advLAR
  have h := abs_sub_le (prRealLAR D lam pp q N d ℓ t label)
    (prZeroSecretReplacedLAR D lam pp q N d ℓ t label) (prIdealLAR D lam pp q N d ℓ t)
  rw [prAlignmentLAR_advantage_scaling] at h
  linarith [zero_cost D lam pp q N d ℓ t label hzero]

end InfoLossLAR.WorstCase.GeneralRank

end P2MDyadicModule114

/- Helper module Solution. -/
section P2MDyadicModule115

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option maxRecDepth 16000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GeneralRank

open scoped BigOperators Classical

open QAlgorithms.Complexity Integration9_9 LARCoinMachine GenericRank

private theorem draws_close (F : RoundingFamily) (D : Family) (hD : IsQPT D) :
    ∃ B : Family, IsQPT B ∧ CallsOnce B D ∧ ∀ (n t : ℕ), 0<t →
      ∀ table : GenericRank.Tables F n t,
      let q := F.q n
      let c := q^(F.N n + t*F.ell n)
      |acceptProb B (encInput n (F.pp n) (encTable table)) -
        avg (fun aux : Fin (F.N n) → ZMod q => avg fun marks : Fin t → Fin (F.ell n) → ZMod q =>
          acceptProb D (rankOneEncodedQuery n (F.pp n) q (F.N n) (F.d n) (F.ell n) t
            (fun u => (F.smith n).J.mulVec u) (aux,marks) table))| ≤ (c:ℝ)/(2:ℝ)^ticketBits c := by
  obtain ⟨B,hB,honce,h⟩ := machine modulus slots applyDigits modulus_poly slots_poly applyDigits_poly D hD
  refine ⟨B,hB,honce,?_⟩
  intro n t ht table
  dsimp only
  let w := encInput n (F.pp n) (encTable table)
  have hm : modulus w = F.q n := modulus_exact F n t ht table
  have hs : (slots w).length = F.N n+t*F.ell n := slots_length F n t ht table
  have count : ticketCount modulus slots w = (F.q n)^(F.N n+t*F.ell n) := by
    rw [ticketCount,LARCoinMachine.powerWithSlots_eq,hm,hs]
  have hp : 0<ticketCount modulus slots w := by rw [count]; exact pow_pos (F.q_prime n).pos _
  have hw := h w hp
  rw [count,hm] at hw
  let test digits := acceptProb D (applyDigits (w,digits))
  have hj := digit_average (F.q n) (F.N n) t (F.ell n) (slots w) hs test
  dsimp only [test] at hj
  rw [hj] at hw
  have hv (aux : Fin (F.N n) → ZMod (F.q n)) (marks : Fin t → Fin (F.ell n) → ZMod (F.q n)) :
      applyDigits (w,joinDigits aux marks) = _ := applyDigits_exact F n t ht table aux marks
  simp_rw [hv] at hw
  exact hw

private theorem absorb {q b ε a p x y : ℝ} (hq : 0≤q)
    (h : x ≤ q*y + a*(1-p)) (herr : |b-y| ≤ 2*ε) (hb : 2*q*ε ≤ a*p) :
    x ≤ q*b+a := by
  have h' : y ≤ b+2*ε := by linarith [(abs_le.mp herr).1]
  have hm := mul_le_mul_of_nonneg_left h' hq
  linarith only [h,hm,hb]

theorem _root_.solution (F : RoundingFamily) (_hF : F.Efficient) (D : Family) (hD : IsQPT D)
    (t : ℕ → ℕ) (ht : ∀ lam, 1 ≤ t lam) (_htp : PolyBoundedFn t) :
    ∃ B : Family, IsQPT B ∧ CallsOnce B D ∧
      ∀ lam : ℕ, 1 ≤ lam →
        F.advLAR D lam (t lam) ≤
          (F.q lam : ℝ) * F.advUZF B lam (t lam) + ((F.q lam : ℝ) ^ F.N lam)⁻¹ := by
  obtain ⟨B,hB,honce,hclose⟩ := draws_close F D hD
  refine ⟨B,hB,honce,?_⟩
  intro n _
  letI : Fact (F.q n).Prime := ⟨F.q_prime n⟩
  let label := (F.smith n).fT
  let dir := (Matrix.mulVecLin (F.smith n).J).toAddMonoidHom
  have h0 : label 0 = 0 := by
    have hz : lift (0 : Fin (F.d n) → ZMod (F.q n)) = 0 := by funext i; simp [lift]
    have hz' : carry (F.q n) (0 : Fin (F.d n) → ℤ) = 0 := by funext i; simp [carry]
    simp only [label,SmithData.fT,AR,hz, Matrix.mulVec_zero,hz']
    funext j
    simp [modq]
  have hd : 1≤ F.d n := (Nat.zero_le _).trans_lt (F.ell_pos n)
  have hTr := (lemma_3_5 _ _ _ (F.q_odd n) hd (F.T n) (F.smith n)).2.2.2.2.2.2.1
  have hres := reserve D n (F.pp n) (F.q n) (F.N n) (F.d n) (F.ell n) (t n)
    label h0 dir hTr
  let c := (F.q n)^(F.N n+t n*F.ell n)
  let δ : ℝ := c/(2:ℝ)^ticketBits c
  have hcomp := GeneralRankComparison.rankOne_error B D n (F.pp n) (F.q n) (F.N n)
    (F.d n) (F.ell n) (t n) (larUniformZeroLaw label h0) dir δ (hclose n (t n) (ht n))
  have hweight : (larUniformZeroLaw label h0).weight = unifZeroFiber label :=
    funext (larUniformZeroLaw_weight _ _ _ label h0)
  rw [hweight] at hcomp
  have hqc : F.q n ≤ c := by
    dsimp [c]
    calc
      F.q n = (F.q n)^1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (F.q_prime n).pos ((F.N_pos n).trans (Nat.le_add_right _ _))
  have hbudget : 2*(F.q n:ℝ)*δ ≤ (c:ℝ)⁻¹ := bit_budget_error (F.q_prime n).pos hqc
  have hsplit : (c:ℝ)⁻¹ = ((F.q n:ℝ)^F.N n)⁻¹ * ((F.q n:ℝ)^(t n*F.ell n))⁻¹ := by
    simp [c,Nat.cast_pow,pow_add,mul_inv_rev,mul_comm]
  rw [hsplit] at hbudget
  exact absorb (Nat.cast_nonneg (F.q n)) hres hcomp hbudget

end InfoLossLAR.WorstCase.GeneralRank

end P2MDyadicModule115
