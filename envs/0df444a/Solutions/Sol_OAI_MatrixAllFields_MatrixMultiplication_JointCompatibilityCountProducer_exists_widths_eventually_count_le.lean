-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityCountProducer.exists_widths_eventually_count_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:26:17.822206+00:00
-- url     : https://prove2.me/submissions/c3c96eca-038e-4acd-9100-73391e5c7e2d

import Mathlib
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_JointCompatibilityRateLimit_exists_window_eventually_count_le

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRateFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped Topology
open Filter

namespace MatrixMultiplication.Foundation

theorem entropyTerm_nonneg {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ entropyTerm p :=
  Real.negMulLog_nonneg hp₀ hp₁

theorem finiteEntropy_nonneg {A : Type*} [Fintype A] (p : A → ℝ)
    (hp₀ : ∀ a, 0 ≤ p a) (hp₁ : ∀ a, p a ≤ 1) : 0 ≤ finiteEntropy p := by
  exact Finset.sum_nonneg fun a _ => entropyTerm_nonneg (hp₀ a) (hp₁ a)

end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointTypeCounts
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointTypeCounts

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology

section Windows

theorem marginal_coordinate_error {A : Type*} [Fintype A]
    (x y : A → ℝ) (η : ℝ) (h : ∀ a, |x a - y a| ≤ η) :
    |(∑ a, x a) - ∑ a, y a| ≤ (Fintype.card A : ℝ) * η := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ a, (x a - y a)| ≤ ∑ a, |x a - y a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : A, η := Finset.sum_le_sum fun a _ => h a
    _ = _ := by simp

theorem exists_entropy_window {A : Type*} [Fintype A]
    (p : A → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : A → ℝ,
      (∀ a, |q a - p a| ≤ δ) → |finiteEntropy q - finiteEntropy p| < ε := by
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
    (continuous_finiteEntropy.continuousAt : ContinuousAt finiteEntropy p) ε hε
  refine ⟨δ / 2, half_pos hδ, fun q hq => ?_⟩
  apply hcont
  rw [dist_pi_lt_iff hδ]
  intro a
  rw [Real.dist_eq]
  exact (hq a).trans_lt (half_lt_self hδ)

end Windows

end MatrixMultiplication.JointTypeCounts

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointCompatibilityEntropyBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open MatrixMultiplication.Foundation
open MatrixMultiplication.JointTypeCounts MatrixMultiplication.JointCompatibilityIncidence
open scoped BigOperators

namespace MatrixMultiplication.JointCompatibilityEntropyBound

attribute [local instance] Classical.propDecidable

section ClassCounts

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos A : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Pos c)] in
theorem fixedClassWords_size (counts : ∀ c, A c → ℕ)
    (w : FixedClassWords Pos A counts) (c : C) :
    Fintype.card (Pos c) = ∑ a, counts c a := by
  calc
    Fintype.card (Pos c) = ∑ a, wordPopulation (w c).val a :=
      (wordPopulation_sum (w c).val).symm
    _ = ∑ a, counts c a := Finset.sum_congr rfl fun a _ => (w c).property a

end ClassCounts

end MatrixMultiplication.JointCompatibilityEntropyBound

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCompatibilityScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCompatibilityScaling

open MatrixMultiplication.Foundation JointTypeCounts JointCompatibilityIncidence
open JointCompatibilityEntropyBound Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {Shape : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]

omit [DecidableEq C] in
theorem sum_baseGroupSize (base : ∀ c, Shape c → ℕ)
    (d : ∀ c, Shape c → Prop) :
    (∑ g, baseGroupSize base d g) = baseTotal base := by
  simp only [baseGroupSize, baseTotal, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  exact Fintype.sum_fiberwise (designatedGroup (d c)) (base c)

end MatrixMultiplication.JointCompatibilityScaling

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointCompatibilityRateLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCompatibilityRateLimit

open MatrixMultiplication.Foundation JointTypeCounts JointCompatibilityIncidence
open JointCompatibilityEntropyBound JointCompatibilityScaling Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape Pair Left Right : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, DecidableEq (Left c)]
  [∀ c, Fintype (Right c)] [∀ c, DecidableEq (Right c)]

omit [DecidableEq C] in
theorem projectedReferenceEntropy_add_const (base : ∀ c, Shape c → ℕ)
    (d : ∀ c, Shape c → Prop) (H : (Σ c, Option (Shape c)) → ℝ) (δ : ℝ) :
    projectedReferenceEntropy base d (fun g => H g + δ) =
      projectedReferenceEntropy base d H + (totalBase base : ℝ) * δ := by
  simp only [projectedReferenceEntropy, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Nat.cast_sum, sum_baseGroupSize, totalBase, baseTotal]

omit [DecidableEq C] [∀ c, DecidableEq (Pair c)] in
theorem compatibilityRate_add_caps (base : ∀ c, Shape c → ℕ)
    (q : ∀ c, Pair c → ℝ) (designatedLeft designatedRight : ∀ c, Shape c → Prop)
    (HL HR : (Σ c, Option (Shape c)) → ℝ) (δ : ℝ) :
    compatibilityRate base q designatedLeft designatedRight
      (fun g => HL g + δ) (fun g => HR g + δ) =
      compatibilityRate base q designatedLeft designatedRight HL HR +
        2 * (totalBase base : ℝ) * δ := by
  simp only [compatibilityRate, projectedReferenceEntropy_add_const]
  ring

omit [Fintype C] [DecidableEq C] in
theorem repeated_positions_card
    (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    (base : ∀ c, Shape c → ℕ) (t : ℕ)
    (w : FixedClassWords Pos Shape (fun c u => t * base c u)) (c : C) :
    Fintype.card (Pos c) = t * baseSize base c := by
  rw [fixedClassWords_size Pos Shape _ w c]
  simp only [baseSize, Finset.mul_sum]

end MatrixMultiplication.JointCompatibilityRateLimit

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_GroupPairWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation
open MatrixMultiplication.JointTypeCounts MatrixMultiplication.JointCompatibilityIncidence

namespace MatrixMultiplication.JointCompatibilityControls

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape A : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem residualBase_mul_center (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) (c : C) (a : A c) :
    (residualBase base d c : ℝ) * residualCenter base d law c a =
      ∑ u : {u : Shape c // ¬d c u}, (base c u.val : ℝ) * law c u.val a := by
  by_cases hr : residualBase base d c = 0
  · have hb (u : {u : Shape c // ¬d c u}) : base c u.val = 0 := by
      have hle : base c u.val ≤ residualBase base d c :=
        Finset.single_le_sum
          (f := fun v : {u : Shape c // ¬d c u} => base c v.val)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
      rw [hr] at hle
      exact Nat.eq_zero_of_le_zero hle
    simp only [hr, Nat.cast_zero, zero_mul, hb, Finset.sum_const_zero]
  · exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hr)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem residualCenter_nonneg (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) (h0 : ∀ c u a, 0 ≤ law c u a)
    (c : C) (a : A c) : 0 ≤ residualCenter base d law c a :=
  div_nonneg (Finset.sum_nonneg fun shape _ =>
    mul_nonneg (Nat.cast_nonneg _) (h0 c shape.val a))
    (Nat.cast_nonneg _)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem residualCenter_le_one (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) (h1 : ∀ c u a, law c u a ≤ 1)
    (c : C) (a : A c) : residualCenter base d law c a ≤ 1 := by
  by_cases hr : residualBase base d c = 0
  · simp only [residualCenter, hr, Nat.cast_zero, div_zero, zero_le_one]
  · have hp : (0 : ℝ) < residualBase base d c := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr)
    apply (div_le_iff₀ hp).mpr
    calc
      (∑ u : {u : Shape c // ¬d c u}, (base c u.val : ℝ) * law c u.val a) ≤
          ∑ u : {u : Shape c // ¬d c u}, (base c u.val : ℝ) * 1 :=
        Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (h1 _ _ _) (Nat.cast_nonneg _)
      _ = 1 * (residualBase base d c : ℝ) := by
        simp only [mul_one, one_mul, residualBase, Nat.cast_sum]

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, DecidableEq (A c)] in
theorem groupCap_nonneg (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ)
    (h0 : ∀ c u a, 0 ≤ law c u a) (h1 : ∀ c u a, law c u a ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (g : Σ c, Option (Shape c)) :
    0 ≤ groupCap base d law ε g := by
  apply add_nonneg _ hε
  rcases g with ⟨c, k⟩
  cases k with
  | some u =>
      exact finiteEntropy_nonneg (law c u) (h0 c u) (h1 c u)
  | none =>
      exact finiteEntropy_nonneg (residualCenter base d law c)
        (residualCenter_nonneg base d law h0 c) (residualCenter_le_one base d law h1 c)

omit [Fintype C] [DecidableEq C] in
theorem residual_card_repeated
    {Pos : C → Type*} [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop) (t : ℕ)
    (w : FixedClassWords Pos Shape (fun c u => t * base c u)) (c : C) :
    Fintype.card {i : Pos c // ¬d c ((w c).val i)} = t * residualBase base d c := by
  have he := (Fintype.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype (w c).val
    (p := fun i => ¬d c ((w c).val i)) (q := fun u => ¬d c u)
    (fun _ => Iff.rfl))).symm
  have hc : Fintype.card {i : Pos c // ¬d c ((w c).val i)} =
      ∑ u : {u : Shape c // ¬d c u}, wordPopulation (w c).val u.val := by
    simpa only [Fintype.card_sigma, wordPopulation] using he
  exact hc.trans (by simp only [(w c).property, residualBase, Finset.mul_sum])

omit [Fintype C] [DecidableEq C] [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem repeated_mixture_balance
    {Pos : C → Type*} [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) (t : ℕ)
    (w : FixedClassWords Pos Shape (fun c u => t * base c u)) (c : C) (a : A c) :
    (Fintype.card {i : Pos c // ¬d c ((w c).val i)} : ℝ) * residualCenter base d law c a =
      (t : ℝ) * totalCenterCount base law c a -
        ∑ u : {u : Shape c // d c u}, (t * base c u.val : ℕ) * law c u.val a := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype (d c)
    (fun u => (base c u : ℝ) * law c u a)
  have hb : (∑ u : {u : Shape c // ¬d c u}, (base c u.val : ℝ) * law c u.val a) =
      totalCenterCount base law c a -
        ∑ u : {u : Shape c // d c u}, (base c u.val : ℝ) * law c u.val a := by
    unfold totalCenterCount
    linarith
  rw [residual_card_repeated, Nat.cast_mul, mul_assoc, residualBase_mul_center, hb]
  simp only [Nat.cast_mul, mul_sub, Finset.mul_sum, mul_assoc]

end MatrixMultiplication.JointCompatibilityControls

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCompatibilityCountProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCompatibilityCountProducer

open MatrixMultiplication.Foundation JointTypeCounts JointCompatibilityIncidence
open JointCompatibilityControls JointCompatibilityScaling JointCompatibilityRateLimit Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

private theorem exists_pos_le_family_inline_MatrixMultiplication_JointCompatibilityCountProducer {K : Type*} [Fintype K]
    (δ : K → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ δ k := by
  classical
  have aux : ∀ s : Finset K, ∃ ε : ℝ, 0 < ε ∧ ∀ k ∈ s, ε ≤ δ k := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert k s hk ih =>
        obtain ⟨ε, hε, hb⟩ := ih
        refine ⟨min (δ k) ε, lt_min (hδ k) hε, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (hb j hj)
  obtain ⟨ε, hε, hb⟩ := aux Finset.univ
  exact ⟨ε, hε, fun k => hb k (Finset.mem_univ k)⟩

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape A : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

omit [DecidableEq C] [∀ c, DecidableEq (Shape c)] [∀ c, DecidableEq (A c)] in
private theorem exists_group_entropy_window_inline_MatrixMultiplication_JointCompatibilityCountProducer (base : ∀ c, Shape c → ℕ)
    (d : ∀ c, Shape c → Prop) (law : ∀ c, Shape c → A c → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (g : Σ c, Option (Shape c)) (q : A g.1 → ℝ),
      (∀ a, |q a - groupCenter base d law g a| ≤ δ) →
      finiteEntropy q ≤ groupCap base d law ε g := by
  have hex : ∀ g : Σ c, Option (Shape c), ∃ δ : ℝ, 0 < δ ∧
      ∀ q : A g.1 → ℝ, (∀ a, |q a - groupCenter base d law g a| ≤ δ) →
        |finiteEntropy q - finiteEntropy (groupCenter base d law g)| < ε :=
    fun g => exists_entropy_window (groupCenter base d law g) hε
  choose δ hδ hw using hex
  obtain ⟨δ₀, hδ₀, hsmall⟩ := exists_pos_le_family_inline_MatrixMultiplication_JointCompatibilityCountProducer δ hδ
  refine ⟨δ₀, hδ₀, ?_⟩
  intro g q hq
  have hh := (abs_lt.mp (hw g q (fun a => (hq a).trans (hsmall g)))).2
  change finiteEntropy q ≤ finiteEntropy (groupCenter base d law g) + ε
  linarith

omit [Fintype C] [DecidableEq C] in
private theorem repeated_residual_width_le_inline_MatrixMultiplication_JointCompatibilityCountProducer
    {Pos : C → Type*} [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (t : ℕ) (w : FixedClassWords Pos Shape (fun c u => t * base c u))
    (χ η δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : ∀ c, η + (designatedBase base d c : ℝ) * χ ≤ δ) (c : C) :
    ((t : ℝ) * η + (∑ u : {u : Shape c // d c u}, ((t * base c u.val : ℕ) : ℝ)) * χ) /
        Fintype.card {i : Pos c // ¬d c ((w c).val i)} ≤ δ := by
  have hsum : (∑ u : {u : Shape c // d c u}, ((t * base c u.val : ℕ) : ℝ)) =
      (t : ℝ) * designatedBase base d c := by
    simp only [Nat.cast_mul, designatedBase, Nat.cast_sum, Finset.mul_sum]
  rw [residual_card_repeated, hsum, Nat.cast_mul]
  by_cases ht : t = 0
  · simpa only [ht, Nat.cast_zero, zero_mul, add_zero, zero_add, zero_div] using hδ
  by_cases hr : residualBase base d c = 0
  · simpa only [hr, Nat.cast_zero, mul_zero, div_zero] using hδ
  have htpos : (0 : ℝ) < t := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ht)
  have hrpos : (0 : ℝ) < residualBase base d c := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr)
  have hrone : (1 : ℝ) ≤ residualBase base d c := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
  have hres : η + (designatedBase base d c : ℝ) * χ ≤ δ * residualBase base d c :=
    (hnum c).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hrone hδ)
  apply (div_le_iff₀ (mul_pos htpos hrpos)).mpr
  calc
    (t : ℝ) * η + ((t : ℝ) * designatedBase base d c) * χ =
        (t : ℝ) * (η + (designatedBase base d c : ℝ) * χ) := by ring
    _ ≤ (t : ℝ) * (δ * residualBase base d c) :=
      mul_le_mul_of_nonneg_left hres htpos.le
    _ = δ * ((t : ℝ) * residualBase base d c) := by ring

omit [DecidableEq C] in
theorem exists_uniform_sideEntropyControl_all_positions
    (Pair : C → Type*) [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
    (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) (part : ∀ c, Pair c → A c)
    (h0 : ∀ c u a, 0 ≤ law c u a) (h1 : ∀ c u a, law c u a ≤ 1)
    {ε χMax ηMax : ℝ} (hε : 0 < ε) (hχMax : 0 < χMax) (hηMax : 0 < ηMax) :
    ∃ χ η : ℝ, 0 < χ ∧ χ ≤ χMax ∧ 0 < η ∧ η ≤ ηMax ∧
      ∀ (t : ℕ) (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
        (pairCounts : ∀ c, Pair c → ℕ)
        (w : FixedClassWords Pos Shape (fun c u => t * base c u)),
        (∀ c a, |((∑ s : {s : Pair c // part c s = a}, pairCounts c s.val : ℕ) : ℝ) -
          (t : ℝ) * totalCenterCount base law c a| ≤ (t : ℝ) * η) →
        Nonempty (SideEntropyControl Pos Shape Pair A (fun c u => t * base c u)
          pairCounts part d law χ (groupCap base d law ε) w) := by
  obtain ⟨δ, hδ, hwindow⟩ := exists_group_entropy_window_inline_MatrixMultiplication_JointCompatibilityCountProducer base d law hε
  let D : ℕ := ∑ c, designatedBase base d c
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hden : 0 < 2 * ((D : ℝ) + 1) := by positivity
  let χ₀ : ℝ := δ / (2 * ((D : ℝ) + 1))
  have hχ₀ : 0 < χ₀ := div_pos hδ hden
  have heq : (2 * ((D : ℝ) + 1)) * χ₀ = δ := mul_div_cancel₀ _ hden.ne'
  have hχδ : χ₀ ≤ δ := by nlinarith [mul_nonneg hD hχ₀.le]
  have hDχ : (D : ℝ) * χ₀ ≤ δ / 2 := by nlinarith
  let χ := min χMax χ₀
  let η := min ηMax (δ / 2)
  have hχ : 0 < χ := lt_min hχMax hχ₀
  have hη : 0 < η := lt_min hηMax (half_pos hδ)
  have hχδ' : χ ≤ δ := (min_le_right _ _).trans hχδ
  have hnum (c : C) : η + (designatedBase base d c : ℝ) * χ ≤ δ := by
    have hc : (designatedBase base d c : ℝ) ≤ D := by
      exact_mod_cast (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c) : designatedBase base d c ≤ ∑ c, designatedBase base d c)
    have hm : (designatedBase base d c : ℝ) * χ ≤ (D : ℝ) * χ₀ :=
      mul_le_mul hc (min_le_right _ _) hχ.le hD
    have he : η ≤ δ / 2 := min_le_right _ _
    linarith
  refine ⟨χ, η, hχ, min_le_left _ _, hη, min_le_left _ _, ?_⟩
  intro t Pos _ _ pairCounts w haggr
  refine ⟨{
    residualLaw := residualCenter base d law
    totalTarget := fun c a => (t : ℝ) * totalCenterCount base law c a
    totalError := fun _ => (t : ℝ) * η
    aggregate_window := haggr
    mixture_balance := repeated_mixture_balance base d law t w
    nonneg := groupCap_nonneg base d law h0 h1 hε.le
    designated_entropy := ?_
    residual_entropy := ?_ }⟩
  · intro c u _ q hq
    exact hwindow ⟨c, some u⟩ q (fun a => (hq a).trans hχδ')
  · intro c q hq
    exact hwindow ⟨c, none⟩ q (fun a => (hq a).trans
      (repeated_residual_width_le_inline_MatrixMultiplication_JointCompatibilityCountProducer base d t w χ η δ hδ.le hnum c))

section PairMarginals

variable {Pair : C → Type*}
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]

omit [DecidableEq C] [∀ c, Fintype (A c)] in
theorem aggregate_error_of_pairWindow
    (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ)
    (law : ∀ c, Shape c → A c → ℝ) (part : ∀ c, Pair c → A c)
    (hbalance : ∀ c a, (baseSize base c : ℝ) *
      (∑ b : {b : Pair c // part c b = a}, q c b.val) = totalCenterCount base law c a)
    (t : ℕ) (ht : 0 < t) (Pos : C → Type*)
    [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    (pairCounts : ∀ c, Pair c → ℕ)
    (w : FixedClassWords Pos Shape (fun c u => t * base c u))
    (z : FixedClassWords Pos Pair pairCounts) {η : ℝ} (hη : 0 ≤ η)
    (hp : PairWindow base q Pos pairCounts η) (c : C) (a : A c) :
    |((∑ b : {b : Pair c // part c b = a}, pairCounts c b.val : ℕ) : ℝ) -
      (t : ℝ) * totalCenterCount base law c a| ≤
      (t : ℝ) * (aggregateCoefficient base Pair : ℝ) * η := by
  by_cases hz : baseSize base c = 0
  · have hsum : (∑ b, pairCounts c b) = 0 := by
      rw [← JointCompatibilityEntropyBound.fixedClassWords_size Pos Pair pairCounts z c,
        repeated_positions_card Pos base t w c, hz, Nat.mul_zero]
    have hcount (b : Pair c) : pairCounts c b = 0 :=
      Nat.eq_zero_of_le_zero ((Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)).trans_eq hsum)
    have hcenter : totalCenterCount base law c a = 0 := by
      rw [← hbalance c a, hz, Nat.cast_zero, zero_mul]
    simpa only [hcount, Finset.sum_const_zero, Nat.cast_zero, hcenter, mul_zero,
      sub_self, abs_zero] using
      mul_nonneg (mul_nonneg (Nat.cast_nonneg t)
        (Nat.cast_nonneg (aggregateCoefficient base Pair))) hη
  have hb : 0 < baseSize base c := Nat.pos_of_ne_zero hz
  have hn : (0 : ℝ) < Fintype.card (Pos c) := by
    rw [repeated_positions_card Pos base t w c, Nat.cast_mul]
    exact mul_pos (Nat.cast_pos.mpr ht) (Nat.cast_pos.mpr hb)
  have hcoord (b : Pair c) :
      |(pairCounts c b : ℝ) - (t : ℝ) * (baseSize base c : ℝ) * q c b| ≤
        (t : ℝ) * (baseSize base c : ℝ) * η := by
    have heq : (Fintype.card (Pos c) : ℝ) *
        ((pairCounts c b : ℝ) / Fintype.card (Pos c) - q c b) =
        (pairCounts c b : ℝ) - (Fintype.card (Pos c) : ℝ) * q c b := by
      rw [mul_sub, mul_div_cancel₀ _ hn.ne']
    have h := calc
      |(pairCounts c b : ℝ) - (Fintype.card (Pos c) : ℝ) * q c b| =
          |(Fintype.card (Pos c) : ℝ) *
            ((pairCounts c b : ℝ) / Fintype.card (Pos c) - q c b)| :=
        congrArg abs heq.symm
      _ = (Fintype.card (Pos c) : ℝ) *
          |(pairCounts c b : ℝ) / Fintype.card (Pos c) - q c b| := by
        rw [abs_mul, abs_of_pos hn]
      _ ≤ (Fintype.card (Pos c) : ℝ) * η :=
        mul_le_mul_of_nonneg_left (hp c hb b) hn.le
    simpa only [repeated_positions_card Pos base t w c, Nat.cast_mul] using h
  have hm := marginal_coordinate_error
    (fun b : {b : Pair c // part c b = a} => (pairCounts c b.val : ℝ))
    (fun b => (t : ℝ) * (baseSize base c : ℝ) * q c b.val)
    ((t : ℝ) * (baseSize base c : ℝ) * η) (fun b => hcoord b.val)
  have hsum : (∑ b : {b : Pair c // part c b = a},
      (t : ℝ) * (baseSize base c : ℝ) * q c b.val) =
      (t : ℝ) * totalCenterCount base law c a := by
    rw [← Finset.mul_sum, mul_assoc, hbalance c a]
  have hm' :
      |((∑ b : {b : Pair c // part c b = a}, pairCounts c b.val : ℕ) : ℝ) -
        (t : ℝ) * totalCenterCount base law c a| ≤
      (Fintype.card {b : Pair c // part c b = a} : ℝ) *
        ((t : ℝ) * (baseSize base c : ℝ) * η) := by
    simpa only [Nat.cast_sum, hsum] using hm
  have hKnat : baseSize base c * Fintype.card {b : Pair c // part c b = a} ≤
      aggregateCoefficient base Pair :=
    (Nat.mul_le_mul_left _ (Fintype.card_subtype_le _)).trans
      (Finset.single_le_sum
        (f := fun d => baseSize base d * Fintype.card (Pair d))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ c))
  have hK : (baseSize base c : ℝ) *
      (Fintype.card {b : Pair c // part c b = a} : ℝ) ≤
      (aggregateCoefficient base Pair : ℝ) := by exact_mod_cast hKnat
  have hmul := mul_le_mul_of_nonneg_left hK (mul_nonneg (Nat.cast_nonneg t) hη)
  nlinarith

end PairMarginals

section CountProducer

variable {Pair Left Right : C → Type*}
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, DecidableEq (Left c)]
  [∀ c, Fintype (Right c)] [∀ c, DecidableEq (Right c)]

theorem exists_widths_eventually_count_le_oai
    (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ)
    (leftPart : ∀ c, Pair c → Left c) (rightPart : ∀ c, Pair c → Right c)
    (designatedLeft designatedRight : ∀ c, Shape c → Prop)
    (leftLaw : ∀ c, Shape c → Left c → ℝ)
    (rightLaw : ∀ c, Shape c → Right c → ℝ)
    (hparts : ∀ c, Function.Injective (fun a : Pair c => (leftPart c a, rightPart c a)))
    (hL0 : ∀ c u a, 0 ≤ leftLaw c u a) (hL1 : ∀ c u a, leftLaw c u a ≤ 1)
    (hR0 : ∀ c u a, 0 ≤ rightLaw c u a) (hR1 : ∀ c u a, rightLaw c u a ≤ 1)
    (hleft : ∀ c a, (baseSize base c : ℝ) *
      (∑ b : {b : Pair c // leftPart c b = a}, q c b.val) =
        totalCenterCount base leftLaw c a)
    (hright : ∀ c a, (baseSize base c : ℝ) *
      (∑ b : {b : Pair c // rightPart c b = a}, q c b.val) =
        totalCenterCount base rightLaw c a)
    {ε χMax ηMax : ℝ} (hε : 0 < ε) (hχMax : 0 < χMax) (hηMax : 0 < ηMax) :
    ∃ χ η : ℝ, 0 < χ ∧ χ ≤ χMax ∧ 0 < η ∧ η ≤ ηMax ∧
      ∀ᶠ t : ℕ in atTop,
        ∀ (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
          (pairCounts : ∀ c, Pair c → ℕ)
          (_ : FixedClassWords Pos Shape (fun c u => t * base c u))
          (z : FixedClassWords Pos Pair pairCounts),
          PairWindow base q Pos pairCounts η →
          (compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
            pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) ≤
            Real.exp ((t : ℝ) *
              (compatibilityRate base q designatedLeft designatedRight
                (groupCap base designatedLeft leftLaw 0)
                (groupCap base designatedRight rightLaw 0) + ε)) ∧
          (0 < compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
            pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z →
            Real.log (compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
              pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) /
              (t : ℝ) ≤ compatibilityRate base q designatedLeft designatedRight
                (groupCap base designatedLeft leftLaw 0)
                (groupCap base designatedRight rightLaw 0) + ε) := by
  let δ : ℝ := ε / (4 * ((totalBase base : ℝ) + 1))
  have hden : 0 < 4 * ((totalBase base : ℝ) + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδeq : (4 * ((totalBase base : ℝ) + 1)) * δ = ε :=
    mul_div_cancel₀ _ hden.ne'
  have hδbound : 2 * (totalBase base : ℝ) * δ ≤ ε / 2 := by nlinarith
  obtain ⟨χL, ηL, hχL, hχLMax, hηL, _, hCL⟩ :=
    exists_uniform_sideEntropyControl_all_positions Pair base designatedLeft leftLaw leftPart
      hL0 hL1 (ηMax := 1) hδ hχMax zero_lt_one
  obtain ⟨χR, ηR, hχR, hχRMax, hηR, _, hCR⟩ :=
    exists_uniform_sideEntropyControl_all_positions Pair base designatedRight rightLaw rightPart
      hR0 hR1 (ηMax := 1) hδ hχMax zero_lt_one
  let χ := min χL χR
  have hχ : 0 < χ := lt_min hχL hχR
  have hχMax' : χ ≤ χMax := (min_le_left _ _).trans hχLMax
  let K : ℕ := aggregateCoefficient base Pair
  have hKden : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  let ηUpper : ℝ := min ηMax (min ηL ηR / ((K : ℝ) + 1))
  have hηUpper : 0 < ηUpper := lt_min hηMax (div_pos (lt_min hηL hηR) hKden)
  obtain ⟨η, hη, hηUpper', hbound⟩ := exists_window_eventually_count_le
    base q leftPart rightPart designatedLeft designatedRight leftLaw rightLaw hparts
    (groupCap base designatedLeft leftLaw δ) (groupCap base designatedRight rightLaw δ)
    (half_pos hε) hηUpper
  have hηMax' : η ≤ ηMax := hηUpper'.trans (min_le_left _ _)
  have hηscale : (K : ℝ) * η ≤ min ηL ηR := by
    have hle : η ≤ min ηL ηR / ((K : ℝ) + 1) :=
      hηUpper'.trans (min_le_right _ _)
    have hmul := (le_div_iff₀ hKden).mp hle
    nlinarith
  have hrate :
      compatibilityRate base q designatedLeft designatedRight
        (groupCap base designatedLeft leftLaw δ) (groupCap base designatedRight rightLaw δ) +
          ε / 2 ≤
      compatibilityRate base q designatedLeft designatedRight
        (groupCap base designatedLeft leftLaw 0) (groupCap base designatedRight rightLaw 0) + ε := by
    have heq := compatibilityRate_add_caps base q designatedLeft designatedRight
      (groupCap base designatedLeft leftLaw 0) (groupCap base designatedRight rightLaw 0) δ
    have hcapL : (fun g => groupCap base designatedLeft leftLaw 0 g + δ) =
        groupCap base designatedLeft leftLaw δ := by
      funext g
      simp only [groupCap, add_zero]
    have hcapR : (fun g => groupCap base designatedRight rightLaw 0 g + δ) =
        groupCap base designatedRight rightLaw δ := by
      funext g
      simp only [groupCap, add_zero]
    rw [hcapL, hcapR] at heq
    linarith only [heq, hδbound]
  refine ⟨χ, η, hχ, hχMax', hη, hηMax', ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with t hb ht
  intro Pos _ _ pairCounts w z hp
  have htpos : 0 < t := lt_of_lt_of_le Nat.zero_lt_one ht
  have haggrL : ∀ c a,
      |((∑ b : {b : Pair c // leftPart c b = a}, pairCounts c b.val : ℕ) : ℝ) -
        (t : ℝ) * totalCenterCount base leftLaw c a| ≤ (t : ℝ) * ηL := by
    intro c a
    have h := aggregate_error_of_pairWindow base q leftLaw leftPart hleft
      t htpos Pos pairCounts w z hη.le hp c a
    have hscale := mul_le_mul_of_nonneg_left
      (hηscale.trans (min_le_left _ _)) (Nat.cast_nonneg t)
    change _ ≤ (t : ℝ) * (K : ℝ) * η at h
    nlinarith
  have haggrR : ∀ c a,
      |((∑ b : {b : Pair c // rightPart c b = a}, pairCounts c b.val : ℕ) : ℝ) -
        (t : ℝ) * totalCenterCount base rightLaw c a| ≤ (t : ℝ) * ηR := by
    intro c a
    have h := aggregate_error_of_pairWindow base q rightLaw rightPart hright
      t htpos Pos pairCounts w z hη.le hp c a
    have hscale := mul_le_mul_of_nonneg_left
      (hηscale.trans (min_le_right _ _)) (Nat.cast_nonneg t)
    change _ ≤ (t : ℝ) * (K : ℝ) * η at h
    nlinarith
  obtain ⟨controlL⟩ := hCL t Pos pairCounts w haggrL
  obtain ⟨controlR⟩ := hCR t Pos pairCounts w haggrR
  have controlL' := control_mono_width (fun c u => t * base c u) pairCounts
    leftPart designatedLeft leftLaw (groupCap base designatedLeft leftLaw δ) w
    controlL (show χ ≤ χL from min_le_left _ _)
  have controlR' := control_mono_width (fun c u => t * base c u) pairCounts
    rightPart designatedRight rightLaw (groupCap base designatedRight rightLaw δ) w
    controlR (show χ ≤ χR from min_le_right _ _)
  have hcount := hb Pos pairCounts w z χ hp controlL' controlR'
  refine ⟨hcount.1.trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg t))), ?_⟩
  intro hpos
  exact (hcount.2 hpos).trans hrate

end CountProducer

end MatrixMultiplication.JointCompatibilityCountProducer

end
end

end MatrixAllFields

end OAI
end

theorem solution.{u_1, u_2, u_4, u_5, u_6, u_7} : type_of% @OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityCountProducer.exists_widths_eventually_count_le_oai.{u_1, u_2, u_4, u_5, u_6, u_7} := @OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityCountProducer.exists_widths_eventually_count_le_oai.{u_1, u_2, u_4, u_5, u_6, u_7}
