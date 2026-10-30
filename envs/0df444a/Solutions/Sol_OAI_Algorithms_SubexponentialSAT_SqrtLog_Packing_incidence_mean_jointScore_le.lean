-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidence_mean_jointScore_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:07:51.199395+00:00
-- url     : https://prove2.me/submissions/46b63628-6c57-4b24-91a4-dff774dc3a7f

import Mathlib
import Definitions.Def_OAIQ081S022
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S078

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Variance
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A finite dependency-graph variance bound

All expectations below are finite rational sums. The main theorem expands the
square of a centered count into a double sum of covariances. Nonneighbors have
zero covariance; at most `d + 1` entries in each row remain, each at most one.
-/

namespace SubexponentialSAT.Variance

open scoped BigOperators

variable {Ω V U : Type*}

section Mean

variable [Fintype Ω] (weight : Ω → ℚ)

theorem mean_add (f g : Ω → ℚ) :
    mean weight (fun ω => f ω + g ω) = mean weight f + mean weight g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

theorem mean_sub (f g : Ω → ℚ) :
    mean weight (fun ω => f ω - g ω) = mean weight f - mean weight g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_mul_const (f : Ω → ℚ) (a : ℚ) :
    mean weight (fun ω => f ω * a) = mean weight f * a := by
  simp [mean, Finset.sum_mul, mul_assoc]

theorem mean_const (hweight : ∑ ω, weight ω = 1) (a : ℚ) :
    mean weight (fun _ => a) = a := by
  rw [mean, ← Finset.sum_mul, hweight, one_mul]

theorem mean_sum {I : Type*} [Fintype I] (f : I → Ω → ℚ) :
    mean weight (fun ω => ∑ i, f i ω) = ∑ i, mean weight (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem mean_mono (hweight : ∀ ω, 0 ≤ weight ω) {f g : Ω → ℚ}
    (hfg : ∀ ω, f ω ≤ g ω) : mean weight f ≤ mean weight g := by
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (hweight ω)

theorem uniformWeight_nonneg (ω : Ω) : 0 ≤ uniformWeight ω := by
  exact div_nonneg (by norm_num) (Nat.cast_nonneg _)

theorem uniformWeight_sum [Nonempty Ω] : ∑ ω : Ω, uniformWeight ω = 1 := by
  have hcard : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [uniformWeight, div_eq_mul_inv, hcard]

end Mean

end SubexponentialSAT.Variance

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_TypeDistribution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform words induce uniform local types

The outcome space consists of all assignments of words to distinct factor,
head, and padding indices. Local read maps are injective. Read maps at
distinct coordinates sharing no factor have disjoint ranges. Finite product
counting then supplies the actual marginals and pair moments needed by
SubexponentialSAT.Variance; these probabilistic properties are conclusions, not hypotheses.
-/

namespace SubexponentialSAT.TypeDistribution

open scoped BigOperators
open SubexponentialSAT.SlotAssignment SubexponentialSAT.Variance

section FiniteMeans

variable {A B I J W : Type*}

theorem mean_prod_mul [Fintype A] [Fintype B] (f : A → ℚ) (g : B → ℚ) :
    mean uniformWeight (fun p : A × B => f p.1 * g p.2) =
      mean uniformWeight f * mean uniformWeight g := by
  rw [mean_uniformWeight, mean_uniformWeight, mean_uniformWeight,
    Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, Fintype.card_prod, Nat.cast_mul]
  exact mul_div_mul_comm _ _ _ _

/-- Functions of disjoint sets of independent uniform coordinates have
factorizing pair moments. -/
theorem mean_restrict_mul [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype W] [Nonempty W]
    (e : A ↪ I) (f : B ↪ I) (h : ∀ a b, e a ≠ f b)
    (F : (A → W) → ℚ) (G : (B → W) → ℚ) :
    mean uniformWeight (fun ω : I → W =>
      F (fun a => ω (e a)) * G (fun b => ω (f b))) =
      mean uniformWeight F * mean uniformWeight G := by
  calc
    _ = mean uniformWeight (fun ξ : A ⊕ B → W =>
        F (fun a => ξ (.inl a)) * G (fun b => ξ (.inr b))) :=
      mean_restrict (jointReads e f h) _
    _ = mean uniformWeight (fun p : (A → W) × (B → W) => F p.1 * G p.2) :=
      mean_equiv (Equiv.sumArrowEquivProdArrow A B W)
        (fun p : (A → W) × (B → W) => F p.1 * G p.2)
    _ = _ := mean_prod_mul F G

end FiniteMeans

section TypeCollisions

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq U]

theorem sum_fiberCount (τ : V → U) :
    (∑ u : U, ((Finset.univ.filter fun v => τ v = u).card : ℚ)) =
      (Fintype.card V : ℚ) := by
  have hc (u : U) :
      ((Finset.univ.filter fun v => τ v = u).card : ℚ) =
        ∑ v : V, if τ v = u then (1 : ℚ) else 0 := by simp
  simp_rw [hc]
  rw [Finset.sum_comm]
  simp

/-- Squared fiber counts count ordered pairs in the same fiber. -/
theorem sum_fiberCount_sq (τ : V → U) :
    (∑ u : U, ((Finset.univ.filter fun v => τ v = u).card : ℚ) ^ 2) =
      ∑ v : V, ∑ w : V, if τ v = τ w then (1 : ℚ) else 0 := by
  have hc (u : U) :
      ((Finset.univ.filter fun v => τ v = u).card : ℚ) =
        ∑ v : V, if τ v = u then (1 : ℚ) else 0 := by simp
  calc
    _ = ∑ u : U, ∑ v : V, ∑ w : V,
        (if τ v = u then (1 : ℚ) else 0) * (if τ w = u then (1 : ℚ) else 0) := by
      simp_rw [hc, pow_two, Finset.sum_mul, Finset.mul_sum]
    _ = ∑ v : V, ∑ w : V, ∑ u : U,
        (if τ v = u then (1 : ℚ) else 0) * (if τ w = u then (1 : ℚ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro w _
      simp [ eq_comm]

/-- The global squared-deviation potential is a sum of local pair-collision
indicators minus a constant. This is the efficient-evaluation interface. -/
theorem squared_deviation_eq_collisions [Nonempty U] (τ : V → U) :
    (∑ u : U, (((Finset.univ.filter fun v => τ v = u).card : ℚ) -
      (Fintype.card V : ℚ) / (Fintype.card U : ℚ)) ^ 2) =
      (∑ v : V, ∑ w : V, if τ v = τ w then (1 : ℚ) else 0) -
        (Fintype.card V : ℚ) ^ 2 / (Fintype.card U : ℚ) := by
  have hN : (Fintype.card U : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hexpand :
      (∑ u : U, (((Finset.univ.filter fun v => τ v = u).card : ℚ) -
        (Fintype.card V : ℚ) / (Fintype.card U : ℚ)) ^ 2) =
      (∑ u : U, ((Finset.univ.filter fun v => τ v = u).card : ℚ) ^ 2) -
        2 * ((Fintype.card V : ℚ) / (Fintype.card U : ℚ)) *
          (∑ u : U, ((Finset.univ.filter fun v => τ v = u).card : ℚ)) +
        (Fintype.card U : ℚ) *
          ((Fintype.card V : ℚ) / (Fintype.card U : ℚ)) ^ 2 := by
    calc
      _ = ∑ u : U,
          (((Finset.univ.filter fun v => τ v = u).card : ℚ) ^ 2 -
          (2 * ((Fintype.card V : ℚ) / (Fintype.card U : ℚ))) *
            ((Finset.univ.filter fun v => τ v = u).card : ℚ) +
          ((Fintype.card V : ℚ) / (Fintype.card U : ℚ)) ^ 2) := by
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hexpand, sum_fiberCount_sq, sum_fiberCount]
  field_simp
  ring

end TypeCollisions

end SubexponentialSAT.TypeDistribution

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingVariance
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact collision-energy bounds used in correlated incidence packing. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.Variance

noncomputable section

variable {Ω I U : Type*} [Fintype Ω] [Fintype I] [Fintype U]
  [DecidableEq I] [DecidableEq U] [Nonempty Ω] [Nonempty U]

omit [DecidableEq I] in
theorem energy_eq_collisions (label : I → U) :
    energy label = (∑ i, ∑ j, if label i = label j then (1 : ℚ) else 0) -
      (Fintype.card I : ℚ)^2 / (Fintype.card U : ℚ) := by
  exact SubexponentialSAT.TypeDistribution.squared_deviation_eq_collisions label

omit [Nonempty U] in
theorem collision_eq_indicator_sum (x y : U) :
    (if x = y then (1 : ℚ) else 0) =
      ∑ u : U, (if x = u then (1 : ℚ) else 0) * (if y = u then 1 else 0) := by
  simp [ ]

omit [Nonempty Ω] in
theorem mean_collision_of_indicators (X Y : Ω → U)
    (h : ∀ u, mean uniformWeight (fun ω =>
      (if X ω = u then (1 : ℚ) else 0) * (if Y ω = u then 1 else 0)) =
        (1 / (Fintype.card U : ℚ)) * (1 / (Fintype.card U : ℚ))) :
    mean uniformWeight (fun ω => if X ω = Y ω then (1 : ℚ) else 0) =
      1 / (Fintype.card U : ℚ) := by
  have hf : (fun ω => if X ω = Y ω then (1 : ℚ) else 0) =
      (fun ω => ∑ u : U, (if X ω = u then (1 : ℚ) else 0) *
        (if Y ω = u then 1 else 0)) := by
    funext ω
    exact collision_eq_indicator_sum (X ω) (Y ω)
  rw [hf, mean_sum]
  simp_rw [h]
  have hN : (Fintype.card U : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Inclusive dependency sets give a bound without a factor of the type count. -/
theorem mean_energy_le (label : Ω → I → U) (deps : I → Finset I) (d : ℕ)
    (hcard : ∀ i, (deps i).card ≤ d)
    (hind : ∀ i j, j ∉ deps i →
      mean uniformWeight (fun ω => if label ω i = label ω j then (1 : ℚ) else 0) =
        1 / (Fintype.card U : ℚ)) :
    mean uniformWeight (fun ω => energy (label ω)) ≤
      (d : ℚ) * (Fintype.card I : ℚ) := by
  let c (i j : I) : ℚ :=
    mean uniformWeight (fun ω => if label ω i = label ω j then (1 : ℚ) else 0) -
      1 / (Fintype.card U : ℚ)
  have hbound (i j : I) : c i j ≤ 1 := by
    have hm : mean uniformWeight
        (fun ω => if label ω i = label ω j then (1 : ℚ) else 0) ≤ 1 := by
      calc
        _ ≤ mean uniformWeight (fun _ : Ω => (1 : ℚ)) := by
          apply mean_mono _ uniformWeight_nonneg
          intro ω
          split_ifs <;> norm_num
        _ = 1 := mean_const _ uniformWeight_sum _
    have hn : 0 ≤ 1 / (Fintype.card U : ℚ) := by positivity
    dsimp [c]
    linarith
  have hrow (i : I) : (∑ j, c i j) ≤ (d : ℚ) := by
    calc
      _ ≤ ∑ j, if j ∈ deps i then (1 : ℚ) else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j ∈ deps i
        · simpa only [ite_eq_left hj] using hbound i j
        · simp [hj, c, hind i j hj]
      _ = ((deps i).card : ℚ) := by simp
      _ ≤ (d : ℚ) := by exact_mod_cast hcard i
  have heq : mean uniformWeight (fun ω => energy (label ω)) = ∑ i, ∑ j, c i j := by
    simp_rw [energy_eq_collisions, mean_sub, mean_sum]
    rw [mean_const _ uniformWeight_sum]
    dsimp [c]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  rw [heq]
  calc
    _ ≤ ∑ _i : I, (d : ℚ) := Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by simp [mul_comm]

end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual shared-head/shared-factor words on an arbitrary finite incidence set. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.Variance SubexponentialSAT.MulticolorTypes

noncomputable section

section Evaluation
variable {J W : Type*} [Fintype J] [DecidableEq J] [Fintype W] [Nonempty W]

theorem mean_eval_mul {j k : J} (h : j ≠ k) (F G : W → ℚ) :
    mean uniformWeight (fun ω : J → W => F (ω j) * G (ω k)) =
      mean uniformWeight F * mean uniformWeight G := by
  calc
    _ = mean uniformWeight (fun ξ : Unit → W => F (ξ ())) *
        mean uniformWeight (fun ξ : Unit → W => G (ξ ())) :=
      SubexponentialSAT.TypeDistribution.mean_restrict_mul (singletonRead j) (singletonRead k)
        (fun _ _ => h) _ _
    _ = _ := congrArg₂ (· * ·)
      (SubexponentialSAT.TypeDistribution.mean_equiv (Equiv.funUnique Unit W) F)
      (SubexponentialSAT.TypeDistribution.mean_equiv (Equiv.funUnique Unit W) G)
end Evaluation

section Incidences
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
theorem incidenceType_eq (ω : WordAssignment V E r Q) (i : I) :
    incidenceType ivar factor ω i =
      twoWordEquiv r Q (fun b => ω (incidenceReads ivar factor i b)) := by
  rfl

omit [Fintype V] [Fintype E] in
theorem dependencySet_card_le (B a : ℕ)
    (hB : ∀ v, (Finset.univ.filter fun i => ivar i = v).card ≤ B)
    (ha : ∀ e, (Finset.univ.filter fun i => factor i = e).card ≤ a) (i : I) :
    (dependencySet ivar factor i).card ≤ B + a - 1 := by
  let X := Finset.univ.filter fun j => ivar j = ivar i
  let Y := Finset.univ.filter fun j => factor j = factor i
  have heq : dependencySet ivar factor i = X ∪ Y := by
    ext j
    simp [dependencySet, X, Y]
  have hi : i ∈ X ∩ Y := by simp [X, Y]
  have hpos : 1 ≤ (X ∩ Y).card := Finset.card_pos.mpr ⟨i, hi⟩
  have hc := Finset.card_union_add_card_inter X Y
  have hx : X.card ≤ B := hB (ivar i)
  have hy : Y.card ≤ a := ha (factor i)
  rw [heq]
  omega

variable [NeZero r]

omit [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceReads_disjoint {i j : I} (h : j ∉ dependencySet ivar factor i) :
    ∀ b c, incidenceReads ivar factor i b ≠ incidenceReads ivar factor j c := by
  have hh : ivar j ≠ ivar i ∧ factor j ≠ factor i := by
    simpa only [mem_dependencySet, not_or] using h
  intro b c
  cases b <;> cases c
  · change Sum.inl (ivar i) ≠ Sum.inl (ivar j)
    exact fun hij => (Ne.symm hh.1) (Sum.inl.inj hij)
  · change Sum.inl (ivar i) ≠ Sum.inr (factor j)
    exact Sum.inl_ne_inr
  · change Sum.inr (factor i) ≠ Sum.inl (ivar j)
    exact Sum.inr_ne_inl
  · change Sum.inr (factor i) ≠ Sum.inr (factor j)
    exact fun hij => (Ne.symm hh.2) (Sum.inr.inj hij)

omit [DecidableEq I] in
theorem mean_incidenceType_mul {i j : I} (h : j ∉ dependencySet ivar factor i)
    (F G : UniversalType r Q 1 → ℚ) :
    mean uniformWeight (fun ω : WordAssignment V E r Q =>
      F (incidenceType ivar factor ω i) * G (incidenceType ivar factor ω j)) =
      mean uniformWeight F * mean uniformWeight G := by
  simp_rw [incidenceType_eq]
  calc
    _ = mean uniformWeight (fun ξ => F (twoWordEquiv r Q ξ)) *
        mean uniformWeight (fun ξ => G (twoWordEquiv r Q ξ)) :=
      SubexponentialSAT.TypeDistribution.mean_restrict_mul
        (incidenceReads ivar factor i) (incidenceReads ivar factor j)
        (incidenceReads_disjoint ivar factor h) _ _
    _ = _ := congrArg₂ (· * ·)
      (SubexponentialSAT.TypeDistribution.mean_equiv (twoWordEquiv r Q) F)
      (SubexponentialSAT.TypeDistribution.mean_equiv (twoWordEquiv r Q) G)

omit [DecidableEq I] in
theorem mean_incidence_collision {i j : I} (h : j ∉ dependencySet ivar factor i) :
    mean uniformWeight (fun ω : WordAssignment V E r Q =>
      if incidenceType ivar factor ω i = incidenceType ivar factor ω j then (1 : ℚ) else 0) =
        1 / (Fintype.card (UniversalType r Q 1) : ℚ) := by
  apply mean_collision_of_indicators
  intro u
  exact (mean_incidenceType_mul ivar factor h
    (fun x => if x = u then (1 : ℚ) else 0)
    (fun x => if x = u then (1 : ℚ) else 0)).trans
      (by rw [SubexponentialSAT.TypeDistribution.mean_indicator])

theorem mean_incidence_energy_le (B a : ℕ)
    (hB : ∀ v, (Finset.univ.filter fun i => ivar i = v).card ≤ B)
    (ha : ∀ e, (Finset.univ.filter fun i => factor i = e).card ≤ a) :
    mean uniformWeight (fun ω : WordAssignment V E r Q =>
      energy (incidenceType ivar factor ω)) ≤
        ((B + a - 1 : ℕ) : ℚ) * (Fintype.card I : ℚ) := by
  exact mean_energy_le _ (dependencySet ivar factor) (B + a - 1)
    (dependencySet_card_le ivar factor B a hB ha)
    (fun _ _ h => mean_incidence_collision ivar factor h)

/-- Original-variable heads remain independent even though incidence heads repeat. -/
theorem mean_head_collision (t : Fin Q) {v w : V} (h : v ≠ w) :
    mean uniformWeight (fun ω : WordAssignment V E r Q =>
      if ω (.inl v) t = ω (.inl w) t then (1 : ℚ) else 0) = 1 / (r : ℚ) := by
  have h' : mean uniformWeight (fun ω : WordAssignment V E r Q =>
      if ω (.inl v) t = ω (.inl w) t then (1 : ℚ) else 0) =
        1 / (Fintype.card (Fin r) : ℚ) := by
    apply mean_collision_of_indicators
    intro g
    have hi : mean uniformWeight (fun a : Word r Q => if a t = g then (1 : ℚ) else 0) =
        1 / (Fintype.card (Fin r) : ℚ) :=
      (mean_eval t (fun x => if x = g then (1 : ℚ) else 0)).trans
        (SubexponentialSAT.TypeDistribution.mean_indicator g)
    exact (mean_eval_mul (J := V ⊕ E) (W := Word r Q)
      (j := Sum.inl v) (k := Sum.inl w) (by simpa using h)
      (fun a => if a t = g then (1 : ℚ) else 0)
      (fun a => if a t = g then (1 : ℚ) else 0)).trans (by rw [hi])
  simpa using h'

theorem mean_head_energy_le (t : Fin Q) :
    mean uniformWeight (fun ω : WordAssignment V E r Q =>
      energy (fun v => ω (.inl v) t)) ≤ (Fintype.card V : ℚ) := by
  have h := mean_energy_le
    (fun (ω : WordAssignment V E r Q) v => ω (.inl v) t)
    (fun v => {v}) 1 (by intro v; simp)
    (by
      intro v w hw
      simpa using mean_head_collision (E := E) (r := r) t (by simpa [eq_comm] using hw))
  simpa using h

theorem mean_headEnergy_le :
    mean uniformWeight (fun ω : WordAssignment V E r Q => headEnergy ω) ≤
      (Q : ℚ) * (Fintype.card V : ℚ) := by
  unfold headEnergy
  rw [mean_sum]
  calc
    _ ≤ ∑ _t : Fin Q, (Fintype.card V : ℚ) :=
      Finset.sum_le_sum fun t _ => mean_head_energy_le t
    _ = _ := by simp

end Incidences
end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Simultaneous type packing and original-variable head balance. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.Variance SubexponentialSAT.MulticolorTypes
noncomputable section

section Joint
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

omit [Nonempty Ω] in
theorem mean_jointScore (X Y : Ω → ℚ) (x y : ℚ) :
    mean uniformWeight (jointScore X Y x y) =
      y^2 * mean uniformWeight X + x^2 * mean uniformWeight Y := by
  unfold jointScore
  simp only [mul_comm (y^2), mul_comm (x^2), mean_add, mean_mul_const]

omit [Nonempty Ω] in
theorem mean_jointScore_le (X Y : Ω → ℚ) (x y A B : ℚ)
    (hX : mean uniformWeight X ≤ A) (hY : mean uniformWeight Y ≤ B)
    (hA : 4*A ≤ x^2) (hB : 4*B ≤ y^2) :
    mean uniformWeight (jointScore X Y x y) ≤ x^2*y^2 := by
  rw [mean_jointScore]
  have hx := mul_le_mul_of_nonneg_left hX (sq_nonneg y)
  have hy := mul_le_mul_of_nonneg_left hY (sq_nonneg x)
  have ha := mul_le_mul_of_nonneg_left hA (sq_nonneg y)
  have hb := mul_le_mul_of_nonneg_left hB (sq_nonneg x)
  nlinarith [mul_nonneg (sq_nonneg x) (sq_nonneg y)]

end Joint

section Incidences
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

/-- Explicit sufficient size conditions for the two simultaneous energy budgets. -/
theorem incidence_mean_jointScore_le_oai (ε : ℚ) (_hε : 0 < ε) (B a : ℕ)
    (hB : ∀ v, (Finset.univ.filter fun i => ivar i = v).card ≤ B)
    (ha : ∀ e, (Finset.univ.filter fun i => factor i = e).card ≤ a)
    (hM : 0 < Fintype.card I) (hn : 0 < Fintype.card V)
    (hlarge : 4*((B+a : ℕ) : ℚ)*(Fintype.card (UniversalType r Q 1) : ℚ)^2 ≤
      ε^2*(Fintype.card I : ℚ))
    (hhead : 16*(Q : ℚ)*(r : ℚ)^2 ≤ (Fintype.card V : ℚ)) :
    mean uniformWeight (jointScore
      (fun ω : WordAssignment V E r Q => energy (incidenceType ivar factor ω))
      headEnergy (ε*(Fintype.card I : ℚ)/(Fintype.card (UniversalType r Q 1) : ℚ))
      ((Fintype.card V : ℚ)/(2*(r : ℚ)))) ≤
      (ε*(Fintype.card I : ℚ)/(Fintype.card (UniversalType r Q 1) : ℚ))^2 *
      ((Fintype.card V : ℚ)/(2*(r : ℚ)))^2 := by
  apply mean_jointScore_le _ _ _ _
    (((B+a-1 : ℕ) : ℚ)*(Fintype.card I : ℚ)) ((Q : ℚ)*Fintype.card V)
    (mean_incidence_energy_le ivar factor B a hB ha) mean_headEnergy_le
  · have hN : (0 : ℚ) < Fintype.card (UniversalType r Q 1) := by
      exact_mod_cast Fintype.card_pos
    have hI : (0 : ℚ) < Fintype.card I := by exact_mod_cast hM
    have hd : ((B+a-1 : ℕ) : ℚ) ≤ ((B+a : ℕ) : ℚ) := by
      exact_mod_cast Nat.sub_le (B+a) 1
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos hN)).mpr
    have hm := mul_le_mul_of_nonneg_right hlarge (le_of_lt hI)
    have hd' := mul_le_mul_of_nonneg_right hd (by positivity :
      0 ≤ 4*(Fintype.card I : ℚ)*(Fintype.card (UniversalType r Q 1) : ℚ)^2)
    nlinarith
  · have hr : (0 : ℚ) < r := by exact_mod_cast Nat.pos_of_neZero r
    have hv : (0 : ℚ) < Fintype.card V := by exact_mod_cast hn
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos (by positivity : (0 : ℚ) < 2*r))).mpr
    have hm := mul_le_mul_of_nonneg_right hhead (le_of_lt hv)
    nlinarith

end Incidences
end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidence_mean_jointScore_le_oai.{u_1, u_2, u_3} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidence_mean_jointScore_le_oai.{u_1, u_2, u_3}
