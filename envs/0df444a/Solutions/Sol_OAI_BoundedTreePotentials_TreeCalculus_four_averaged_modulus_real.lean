-- Prove2me | solution 1 for OAI.BoundedTreePotentials.TreeCalculus.four_averaged_modulus_real
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T18:24:38.956931+00:00
-- url     : https://prove2.me/submissions/ad44a25b-c586-49b6-b8eb-bd4f78c308e1

import Mathlib
import Definitions.Def_BoundedTreePotentials
import Definitions.Def_OAIQWBTP000

section
-- module Solutions.OAIQW_BoundedTreePotentials.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.TestNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section TestNorms
open scoped Classical
variable {I : Type*}

/-- Symmetry identifies the signed-evaluation supremum with the absolute-pairing norm. -/

theorem testNorm_signed_sup (K : TestFamily I) (x : I →₀ ℝ) :
    testNorm K x = ⨆ f : K, finitePairing f.val x := by
  have hb : BddAbove (range fun f : K => finitePairing f.val x) :=
    ⟨testNorm K x, by rintro _ ⟨f, rfl⟩; exact (le_abs_self _).trans (finitePairing_le_testNorm K f x)⟩
  apply le_antisymm
  · apply ciSup_le
    intro f
    rw [abs_le]
    constructor
    · have hn := le_ciSup hb (⟨-f.val, K.neg_mem _ f.property⟩ : K)
      have he : finitePairing (-f.val) x = -finitePairing f.val x := by
        simp only [finitePairing_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
      rw [he] at hn
      linarith
    · exact le_ciSup hb f
  · apply ciSup_le
    intro f
    exact (le_abs_self _).trans (finitePairing_le_testNorm K f x)

end TestNorms


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.Inward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section InwardScalarCalculus

lemma inward_difference (c v : ℝ) : inwardOne c v - inwardTwo c v = v := by
  unfold inwardOne inwardTwo
  split_ifs <;> rw [sub_neg_eq_add]
  · simp
  · simp

lemma inwardOne_abs_le (c v : ℝ) : |inwardOne c v| ≤ |v| := by
  unfold inwardOne
  split_ifs
  · by_cases h : v ≤ 0
    · simp [min_eq_left h]
    · simp [min_eq_right (le_of_not_ge h)]
  · by_cases h : v ≤ 0
    · simp [max_eq_right h]
    · simp [max_eq_left (le_of_not_ge h)]

lemma inwardTwo_abs_le (c v : ℝ) : |inwardTwo c v| ≤ |v| := by
  unfold inwardTwo
  split_ifs <;> rw [abs_neg]
  · by_cases h : v ≤ 0
    · simp [max_eq_right h]
    · simp [max_eq_left (le_of_not_ge h)]
  · by_cases h : v ≤ 0
    · simp [min_eq_left h]
    · simp [min_eq_right (le_of_not_ge h)]

lemma inwardOne_sub_le (c v w : ℝ) :
    |inwardOne c v - inwardOne c w| ≤ |v - w| := by
  unfold inwardOne
  split_ifs
  · simpa only [Real.dist_eq, one_mul, id_eq, NNReal.coe_one] using
      ((LipschitzWith.id.min_const 0).dist_le_mul v w)
  · exact abs_max_sub_max_le_abs v w 0

lemma inwardTwo_sub_le (c v w : ℝ) :
    |inwardTwo c v - inwardTwo c w| ≤ |v - w| := by
  unfold inwardTwo
  split_ifs <;> rw [neg_sub_neg, abs_sub_comm]
  · exact abs_max_sub_max_le_abs v w 0
  · simpa only [Real.dist_eq, one_mul, id_eq, NNReal.coe_one] using
      ((LipschitzWith.id.min_const 0).dist_le_mul v w)

lemma opposite_sum_bound {c u a b l μ : ℝ} (hc : |c| ≤ a) (hu : |u| ≤ b)
    (hl : 0 ≤ l) (hμ : 0 ≤ μ)
    (hopp : (0 ≤ c → u ≤ 0) ∧ (c < 0 → 0 ≤ u)) :
    |l * c + μ * u| ≤ max (l * a) (μ * b) := by
  rw [abs_le] at hc hu ⊢
  by_cases h : 0 ≤ c
  · have hu0 := hopp.1 h
    constructor
    · have ha := le_max_right (l * a) (μ * b)
      have hm := mul_le_mul_of_nonneg_left hu.1 hμ
      have hl := mul_nonneg hl h
      linarith
    · have ha := le_max_left (l * a) (μ * b)
      have hm := mul_nonpos_of_nonneg_of_nonpos hμ hu0
      have hl := mul_le_mul_of_nonneg_left hc.2 hl
      linarith
  · have hc0 : c < 0 := lt_of_not_ge h
    have hu0 := hopp.2 hc0
    constructor
    · have ha := le_max_left (l * a) (μ * b)
      have hl := mul_le_mul_of_nonneg_left hc.1 hl
      have hm := mul_nonneg hμ hu0
      linarith
    · have ha := le_max_right (l * a) (μ * b)
      have hl := mul_nonpos_of_nonneg_of_nonpos hl hc0.le
      have hm := mul_le_mul_of_nonneg_left hu.2 hμ
      linarith

lemma inwardOne_combination_bound {c v a b l μ : ℝ} (hc : |c| ≤ a) (hv : |v| ≤ b)
    (hl : 0 ≤ l) (hμ : 0 ≤ μ) :
    |l * c + μ * inwardOne c v| ≤ max (l * a) (μ * b) := by
  apply opposite_sum_bound hc ((inwardOne_abs_le c v).trans hv) hl hμ
  constructor
  · intro h; simp only [inwardOne, ite_eq_left h]; exact min_le_right _ _
  · intro h; simp only [inwardOne, ite_eq_right (not_le.mpr h)]; exact le_max_right _ _

lemma inwardTwo_combination_bound {c v a b l μ : ℝ} (hc : |c| ≤ a) (hv : |v| ≤ b)
    (hl : 0 ≤ l) (hμ : 0 ≤ μ) :
    |l * c + μ * inwardTwo c v| ≤ max (l * a) (μ * b) := by
  apply opposite_sum_bound hc ((inwardTwo_abs_le c v).trans hv) hl hμ
  constructor
  · intro h; simp only [inwardTwo, ite_eq_left h]; exact neg_nonpos.mpr (le_max_right _ _)
  · intro h; simp only [inwardTwo, ite_eq_right (not_le.mpr h)]; exact neg_nonneg.mpr (min_le_right _ _)

lemma combined_quadratic_budget {J : Type*} (B : Finset J) (f u : J → ℝ)
    {a θ : ℝ} (hf : ∑ j ∈ B, f j ^ 2 ≤ 1) (hu : ∑ j ∈ B, u j ^ 2 ≤ 1)
    (hd : ∀ j ∈ B, f j = 0 ∨ u j = 0) (hbudget : a^2 + θ^2 ≤ 1) :
    ∑ j ∈ B, (a * f j + θ * u j)^2 ≤ 1 := by
  have he : (∑ j ∈ B, (a * f j + θ * u j)^2) =
      a^2 * (∑ j ∈ B, f j ^ 2) + θ^2 * (∑ j ∈ B, u j ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rcases hd j hj with h | h <;> simp [h, mul_pow]
  rw [he]
  nlinarith [sq_nonneg a, sq_nonneg θ,
    mul_le_mul_of_nonneg_left hf (sq_nonneg a), mul_le_mul_of_nonneg_left hu (sq_nonneg θ)]

end InwardScalarCalculus

namespace TreeCalculus

lemma potential_add (f g : Node → ℝ) (s : Node) :
    potential (f + g) s = potential f s + potential g s := by
  exact List.sum_map_add

lemma potential_sub (f g : Node → ℝ) (s : Node) :
    potential (f - g) s = potential f s - potential g s := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s j ih => simp only [potential_child, ih, Pi.sub_apply]; ring

lemma potential_tail_on_head {D : Set Node} (hD : Initial D) (g : Node → ℝ)
    {s : Node} (hs : s ∈ D) : potential (tailPart D g) s = 0 := by
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
  have h := hD hs ((List.mem_inits r s).mp hr)
  simp [tailPart, h]

lemma potential_head_child {D : Set Node} {h : Node → ℝ}
    (hsupp : ∀ s, s ∉ D → h s = 0) {s : Node} {j : ℕ} (hs : s ++ [j] ∉ D) :
    potential h (s ++ [j]) = potential h s := by
  rw [potential_child, hsupp _ hs, add_zero]


lemma potential_head_on_head {D : Set Node} (hD : Initial D) (g : Node → ℝ)
    {s : Node} (hs : s ∈ D) : potential (headPart D g) s = potential g s := by
  induction s using List.reverseRecOn with
  | nil => simp [headPart, hs]
  | append_singleton s j ih =>
    have hp : s ∈ D := hD hs (List.prefix_append s [j])
    rw [potential_child, potential_child, ih hp]
    simp [headPart, hs]

lemma head_potential_bound {D : Set Node} (hD : Initial D) {g : Node → ℝ}
    {b : ℝ} (hb : 0 ≤ b) (hg : ∀ s, |potential g s| ≤ b) :
    ∀ s, |potential (headPart D g) s| ≤ b := by
  intro s
  induction s using List.reverseRecOn with
  | nil =>
    by_cases h : [] ∈ D
    · simpa only [potential_head_on_head hD g h] using hg []
    · simpa [headPart, h] using hb
  | append_singleton s j ih =>
    by_cases h : s ++ [j] ∈ D
    · simpa only [potential_head_on_head hD g h] using hg (s ++ [j])
    · simpa [potential_child, headPart, h] using ih

lemma tail_eq_sub_head (D : Set Node) (g : Node → ℝ) : tailPart D g = g - headPart D g := by
  classical
  funext s
  by_cases hs : s ∈ D <;> simp [tailPart, headPart, hs]

lemma tail_potential_bound {D : Set Node} (hD : Initial D) {g : Node → ℝ}
    {b : ℝ} (hb : 0 ≤ b) (hg : ∀ s, |potential g s| ≤ b) (s : Node) :
    |potential (tailPart D g) s| ≤ 2 * b := by
  rw [tail_eq_sub_head, potential_sub]
  exact (abs_sub _ _).trans (by linarith [hg s, head_potential_bound hD hb hg s])

lemma inwardCoeffsOne_on_head {D : Set Node} (hD : Initial D) (h g : Node → ℝ)
    {s : Node} (hs : s ∈ D) : inwardCoeffsOne D h g s = 0 := by
  cases s using List.reverseRecOn with
  | nil => simp [inwardCoeffsOne, inwardPotentialOne, potential_tail_on_head hD g hs]
  | append_singleton s j =>
    have hp : s ∈ D := hD hs (List.prefix_append s [j])
    simp [inwardCoeffsOne, inwardPotentialOne, potential_tail_on_head hD g hs,
      potential_tail_on_head hD g hp]

lemma inwardCoeffsTwo_on_head {D : Set Node} (hD : Initial D) (h g : Node → ℝ)
    {s : Node} (hs : s ∈ D) : inwardCoeffsTwo D h g s = 0 := by
  cases s using List.reverseRecOn with
  | nil => simp [inwardCoeffsTwo, inwardPotentialTwo, potential_tail_on_head hD g hs]
  | append_singleton s j =>
    have hp : s ∈ D := hD hs (List.prefix_append s [j])
    simp [inwardCoeffsTwo, inwardPotentialTwo, potential_tail_on_head hD g hs,
      potential_tail_on_head hD g hp]

lemma inwardCoeffs_difference (D : Set Node) (h g : Node → ℝ) (s : Node) :
    inwardCoeffsOne D h g s - inwardCoeffsTwo D h g s = tailPart D g s := by
  cases s using List.reverseRecOn with
  | nil => simpa [inwardCoeffsOne, inwardCoeffsTwo, inwardPotentialOne, inwardPotentialTwo] using
      inward_difference (h []) (tailPart D g [])
  | append_singleton s j =>
    unfold inwardCoeffsOne inwardCoeffsTwo
    rw [increments_child, increments_child]
    change (inwardOne _ _ - inwardOne _ _) - (inwardTwo _ _ - inwardTwo _ _) = _
    rw [show ∀ a b c d : ℝ, (a - b) - (c - d) = (a - c) - (b - d) by intros; ring]
    rw [inward_difference, inward_difference, potential_child]
    ring

lemma inwardCoeffsOne_abs_le {D : Set Node} (hD : Initial D) {h : Node → ℝ}
    (hsupp : ∀ s, s ∉ D → h s = 0) (g : Node → ℝ) (s : Node) :
    |inwardCoeffsOne D h g s| ≤ |g s| := by
  by_cases hd : s ∈ D
  · simp [inwardCoeffsOne_on_head hD h g hd]
  · cases s using List.reverseRecOn with
    | nil =>
      simpa [inwardCoeffsOne, inwardPotentialOne, tailPart, hd] using
        inwardOne_abs_le (h []) (g [])
    | append_singleton s j =>
      unfold inwardCoeffsOne
      rw [increments_child]
      unfold inwardPotentialOne
      rw [potential_head_child hsupp hd]
      have hh := inwardOne_sub_le (potential h s) (potential (tailPart D g) (s ++ [j]))
        (potential (tailPart D g) s)
      simpa [potential_child, tailPart, hd] using hh

lemma inwardCoeffsTwo_abs_le {D : Set Node} (hD : Initial D) {h : Node → ℝ}
    (hsupp : ∀ s, s ∉ D → h s = 0) (g : Node → ℝ) (s : Node) :
    |inwardCoeffsTwo D h g s| ≤ |g s| := by
  by_cases hd : s ∈ D
  · simp [inwardCoeffsTwo_on_head hD h g hd]
  · cases s using List.reverseRecOn with
    | nil =>
      simpa [inwardCoeffsTwo, inwardPotentialTwo, tailPart, hd] using
        inwardTwo_abs_le (h []) (g [])
    | append_singleton s j =>
      unfold inwardCoeffsTwo
      rw [increments_child]
      unfold inwardPotentialTwo
      rw [potential_head_child hsupp hd]
      have hh := inwardTwo_sub_le (potential h s) (potential (tailPart D g) (s ++ [j]))
        (potential (tailPart D g) s)
      simpa [potential_child, tailPart, hd] using hh

end TreeCalculus


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section TestCompletions
open scoped Classical
variable {I : Type*}

lemma norm_testVector_equiv (K : TestFamily I) (x : TestVector K) :
    ‖x‖ = testNorm K ((testVectorEquiv K) x) := rfl

lemma norm_test_single (K : TestFamily I) (i : I) :
    ‖(testVectorEquiv K).symm (Finsupp.single i 1)‖ = 1 := by
  apply le_antisymm
  · change testNorm K (Finsupp.single i 1) ≤ 1
    simpa using testNorm_le_l1 K (Finsupp.single i 1)
  · change 1 ≤ testNorm K (Finsupp.single i 1)
    simpa using coordinate_le_testNorm K (Finsupp.single i 1) i

lemma finiteTestFunctional_norm_le (K : TestFamily I) (f : K) : ‖finiteTestFunctional K f‖ ≤ 1 := by
  refine (finiteTestFunctional K f).opNorm_le_bound zero_le_one ?_
  intro x
  change |finitePairing f.val ((testVectorEquiv K) x)| ≤ 1 * testNorm K ((testVectorEquiv K) x)
  simpa only [one_mul] using finitePairing_le_testNorm K f ((testVectorEquiv K) x)

lemma completedTestFunctional_norm_le (K : TestFamily I) (f : K) :
    ‖completedTestFunctional K f‖ ≤ 1 := by
  have h := (finiteTestFunctional K f).opNorm_extend_le (N := 1)
    (e := UniformSpace.Completion.toComplL) UniformSpace.Completion.denseRange_coe
    (fun x => by simp)
  have h' : ‖completedTestFunctional K f‖ ≤ ‖finiteTestFunctional K f‖ := by
    simpa only [NNReal.coe_one, one_mul, completedTestFunctional] using h
  exact h'.trans (finiteTestFunctional_norm_le K f)

lemma completedTestFunctional_abs_le (K : TestFamily I) (f : K) (x : TestCompletion K) :
    |completedTestFunctional K f x| ≤ ‖x‖ := by
  simpa only [one_mul, Real.norm_eq_abs] using
    (completedTestFunctional K f).le_of_opNorm_le (completedTestFunctional_norm_le K f) x

/-- Extended tests really remain norming; this is established, not postulated
    as an extra hypothesis on the completion. -/
lemma exists_completed_test_near_norm (K : TestFamily I) (x : TestCompletion K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : K, ‖x‖ - ε < completedTestFunctional K f x := by
  obtain ⟨w, hw⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x
    (show 0 < ε / 3 by linarith)
  have hw' : ‖x - (w : TestCompletion K)‖ < ε / 3 := by simpa only [dist_eq_norm] using hw
  have hn : ‖x‖ - ‖w‖ < ε / 3 := by
    have h := norm_sub_norm_le x (w : TestCompletion K)
    rw [UniformSpace.Completion.norm_coe] at h
    exact h.trans_lt hw'
  have hu : testNorm K ((testVectorEquiv K) w) - ε / 3 <
      ⨆ f : K, finitePairing f.val ((testVectorEquiv K) w) := by
    rw [← testNorm_signed_sup K ((testVectorEquiv K) w)]
    linarith
  obtain ⟨f, hf⟩ := exists_lt_of_lt_ciSup hu
  refine ⟨f, ?_⟩
  have hd := completedTestFunctional_abs_le K f (x - (w : TestCompletion K))
  rw [map_sub, completedTestFunctional_coe] at hd
  have hl := (abs_le.mp hd).1
  change ‖w‖ - ε / 3 < finitePairing f.val w at hf
  linarith

theorem completed_tests_norming (K : TestFamily I) (x : TestCompletion K) :
    ‖x‖ = ⨆ f : K, completedTestFunctional K f x := by
  have hb : BddAbove (range fun f : K => completedTestFunctional K f x) :=
    ⟨‖x‖, by rintro _ ⟨f, rfl⟩; exact (le_abs_self _).trans (completedTestFunctional_abs_le K f x)⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨f, hf⟩ := exists_completed_test_near_norm K x hε
    have := le_ciSup hb f
    linarith
  · apply ciSup_le
    intro f
    exact (le_abs_self _).trans (completedTestFunctional_abs_le K f x)

end TestCompletions


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.TreeTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

namespace TreeCalculus
open scoped Classical

lemma coefficientSupport_combine {k : QuadraticKind} {f g : Node → ℝ}
    (hf : CoefficientSupport k f) (hg : CoefficientSupport k g) (a b : ℝ) :
    CoefficientSupport k (a • f + b • g) := by
  cases k with
  | sibling => trivial
  | antichain =>
    apply (hf.union hg).subset
    intro s hs
    change a * f s + b * g s ≠ 0 at hs
    change f s ≠ 0 ∨ g s ≠ 0
    by_contra hh
    push Not at hh
    exact hs (by rw [hh.1, hh.2]; ring)
  | global => exact (hf.const_smul a).add (hg.const_smul b)


lemma headPart_abs_le (D : Set Node) (f : Node → ℝ) (s : Node) : |headPart D f s| ≤ |f s| := by
  by_cases h : s ∈ D <;> simp [headPart, h]

lemma head_isTreeTest {r : Bool} {k : QuadraticKind} {f : Node → ℝ}
    (hf : IsTreeTest r k f) {D : Set Node} (hD : Initial D) :
    IsTreeTest r k (headPart D f) := by
  constructor
  · intro hr; simp [headPart, hf.root_zero hr]
  · exact head_potential_bound hD zero_le_one hf.potential_bound
  · exact quadraticBudget_dominate hf.quadratic_budget (headPart_abs_le D f)
  · exact coefficientSupport_dominate hf.coefficient_support (headPart_abs_le D f)

lemma inwardOne_isTreeTest {r : Bool} {k : QuadraticKind} {h g : Node → ℝ}
    (hh : IsTreeTest r k h) (hg : IsTreeTest r k g) {D : Set Node} (hD : Initial D)
    (hroot : [] ∈ D) (hsupp : ∀ s, s ∉ D → h s = 0)
    {a θ : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (hsquare : a^2 + θ^2 ≤ 1) :
    IsTreeTest r k (a • h + θ • inwardCoeffsOne D h g) := by
  constructor
  · intro hr
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hh.root_zero hr,
      inwardCoeffsOne_on_head hD h g hroot, mul_zero, add_zero]
  · intro s
    rw [potential_add, potential_smul, potential_smul]
    change |a * potential h s + θ * potential (increments (inwardPotentialOne D h g)) s| ≤ 1
    rw [potential_increments]
    exact (inwardOne_combination_bound (hh.potential_bound s)
      (tail_potential_bound hD zero_le_one hg.potential_bound s) ha hθ).trans
      (by apply max_le <;> nlinarith)
  · intro B hB
    apply combined_quadratic_budget
    · exact hh.quadratic_budget B hB
    · exact quadraticBudget_dominate hg.quadratic_budget (inwardCoeffsOne_abs_le hD hsupp g) B hB
    · intro s hs
      by_cases hd : s ∈ D
      · exact Or.inr (inwardCoeffsOne_on_head hD h g hd)
      · exact Or.inl (hsupp s hd)
    · exact hsquare
  · exact coefficientSupport_combine hh.coefficient_support
      (coefficientSupport_dominate hg.coefficient_support (inwardCoeffsOne_abs_le hD hsupp g)) a θ

lemma inwardTwo_isTreeTest {r : Bool} {k : QuadraticKind} {h g : Node → ℝ}
    (hh : IsTreeTest r k h) (hg : IsTreeTest r k g) {D : Set Node} (hD : Initial D)
    (hroot : [] ∈ D) (hsupp : ∀ s, s ∉ D → h s = 0)
    {a θ : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (hsquare : a^2 + θ^2 ≤ 1) :
    IsTreeTest r k (a • h + θ • inwardCoeffsTwo D h g) := by
  constructor
  · intro hr
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hh.root_zero hr,
      inwardCoeffsTwo_on_head hD h g hroot, mul_zero, add_zero]
  · intro s
    rw [potential_add, potential_smul, potential_smul]
    change |a * potential h s + θ * potential (increments (inwardPotentialTwo D h g)) s| ≤ 1
    rw [potential_increments]
    exact (inwardTwo_combination_bound (hh.potential_bound s)
      (tail_potential_bound hD zero_le_one hg.potential_bound s) ha hθ).trans
      (by apply max_le <;> nlinarith)
  · intro B hB
    apply combined_quadratic_budget
    · exact hh.quadratic_budget B hB
    · exact quadraticBudget_dominate hg.quadratic_budget (inwardCoeffsTwo_abs_le hD hsupp g) B hB
    · intro s hs
      by_cases hd : s ∈ D
      · exact Or.inr (inwardCoeffsTwo_on_head hD h g hd)
      · exact Or.inl (hsupp s hd)
    · exact hsquare
  · exact coefficientSupport_combine hh.coefficient_support
      (coefficientSupport_dominate hg.coefficient_support (inwardCoeffsTwo_abs_le hD hsupp g)) a θ



lemma treePairing_congr {r : Bool} {f g : Node → ℝ} (x : TreeCoordinate r →₀ ℝ)
    (h : ∀ s, x s ≠ 0 → f s.val = g s.val) : treePairing f x = treePairing g x := by
  change (∑ s ∈ x.support, x s * f s.val) = (∑ s ∈ x.support, x s * g s.val)
  apply Finset.sum_congr rfl
  intro s hs
  rw [h s (Finsupp.mem_support_iff.mp hs)]

lemma treePairing_zero_of_disjoint {r : Bool} {f : Node → ℝ} (x : TreeCoordinate r →₀ ℝ)
    (h : ∀ s, x s ≠ 0 → f s.val = 0) : treePairing f x = 0 := by
  change (∑ s ∈ x.support, x s * f s.val) = 0
  apply Finset.sum_eq_zero
  intro s hs
  rw [h s (Finsupp.mem_support_iff.mp hs), mul_zero]

lemma treePairing_le_norm {r : Bool} {k : QuadraticKind} {f : Node → ℝ}
    (hf : IsTreeTest r k f) (x : TreeCoordinate r →₀ ℝ) :
    treePairing f x ≤ testNorm (treeTestFamily r k) x :=
  (le_abs_self _).trans (finitePairing_le_testNorm _ (asTreeTest f hf) x)

lemma treePairing_head_eq {r : Bool} (D : Set Node) (f : Node → ℝ) (x : TreeCoordinate r →₀ ℝ)
    (hx : ∀ s, x s ≠ 0 → s.val ∈ D) : treePairing (headPart D f) x = treePairing f x := by
  apply treePairing_congr
  intro s hs
  exact Set.indicator_of_mem (hx s hs) f

lemma treePairing_tail_eq {r : Bool} (D : Set Node) (f : Node → ℝ) (y : TreeCoordinate r →₀ ℝ)
    (hy : ∀ s, s.val ∈ D → y s = 0) : treePairing (tailPart D f) y = treePairing f y := by
  apply treePairing_congr
  intro s hs
  have hd : s.val ∉ D := fun hd => hs (hy s hd)
  exact Set.indicator_of_mem hd f

lemma inward_pairing_identity {r : Bool} {D : Set Node} (hD : Initial D) {h g : Node → ℝ}
    (hsupp : ∀ s, s ∉ D → h s = 0) (x y : TreeCoordinate r →₀ ℝ)
    (hx : ∀ s, x s ≠ 0 → s.val ∈ D) (hy : ∀ s, s.val ∈ D → y s = 0)
    (a θ t : ℝ) :
    treePairing (a • h + θ • inwardCoeffsOne D h g) (x + t • y) +
      treePairing (a • h + θ • inwardCoeffsTwo D h g) (x - t • y) =
      2 * a * treePairing h x + t * θ * treePairing g y := by
  have hhy : treePairing h y = 0 := treePairing_zero_of_disjoint y (by
    intro s hs
    exact hsupp s.val (fun hd => hs (hy s hd)))
  have hu : treePairing (inwardCoeffsOne D h g) x = 0 :=
    treePairing_zero_of_disjoint x (fun s hs => inwardCoeffsOne_on_head hD h g (hx s hs))
  have hv : treePairing (inwardCoeffsTwo D h g) x = 0 :=
    treePairing_zero_of_disjoint x (fun s hs => inwardCoeffsTwo_on_head hD h g (hx s hs))
  have huv : treePairing (inwardCoeffsOne D h g) y - treePairing (inwardCoeffsTwo D h g) y =
      treePairing g y := by
    rw [← treePairing_sub_coeff]
    have he : inwardCoeffsOne D h g - inwardCoeffsTwo D h g = tailPart D g :=
      funext (inwardCoeffs_difference D h g)
    rw [he, treePairing_tail_eq D g y hy]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, treePairing_add_coeff, treePairing_smul_coeff,
    hhy, hu, hv]
  rw [← huv]
  ring

/-- The finite-array form of the paired inward inequality. The proof takes
    suprema instead of presuming an attained infinite-dimensional polar norm. -/
theorem paired_finite_test_bound {r : Bool} {k : QuadraticKind} {D : Set Node}
    (hD : Initial D) (hroot : [] ∈ D)
    (x y : TreeCoordinate r →₀ ℝ)
    (hx : ∀ s, x s ≠ 0 → s.val ∈ D) (hy : ∀ s, s.val ∈ D → y s = 0)
    {a θ t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (hsquare : a^2 + θ^2 ≤ 1)
    (f g : treeTestFamily r k) :
    a * finitePairing f.val x + (t * θ / 2) * finitePairing g.val y ≤
      (testNorm (treeTestFamily r k) (x + t • y) + testNorm (treeTestFamily r k) (x - t • y)) / 2 := by
  let h := headPart D (liftCoefficients r f.val)
  let g' := liftCoefficients r g.val
  have hh : IsTreeTest r k h := head_isTreeTest f.property hD
  have hg : IsTreeTest r k g' := g.property
  have hsupp : ∀ s, s ∉ D → h s = 0 := by intro s hs; exact Set.indicator_of_notMem hs _
  have hplus := treePairing_le_norm (inwardOne_isTreeTest hh hg hD hroot hsupp ha ha1 hθ hθ1 hsquare) (x + t • y)
  have hminus := treePairing_le_norm (inwardTwo_isTreeTest hh hg hD hroot hsupp ha ha1 hθ hθ1 hsquare) (x - t • y)
  have he := inward_pairing_identity (g := g') hD hsupp x y hx hy a θ t
  have hfx : treePairing h x = finitePairing f.val x := by
    change treePairing (headPart D (liftCoefficients r f.val)) x = _
    rw [treePairing_head_eq D _ x hx, treePairing_lift]
  have hgy : treePairing g' y = finitePairing g.val y := treePairing_lift g.val y
  rw [hfx, hgy] at he
  linarith

end TreeCalculus

lemma testNorm_weighted_sup {I : Type*} (K : TestFamily I) (x y : I →₀ ℝ)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ f g : K, a * finitePairing f.val x + b * finitePairing g.val y ≤ c) :
    a * testNorm K x + b * testNorm K y ≤ c := by
  have hba : BddAbove (range fun f : K => a * finitePairing f.val x) :=
    ⟨a * testNorm K x, by
      rintro _ ⟨f, rfl⟩
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (finitePairing_le_testNorm K f x)) ha⟩
  have hbb : BddAbove (range fun f : K => b * finitePairing f.val y) :=
    ⟨b * testNorm K y, by
      rintro _ ⟨f, rfl⟩
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (finitePairing_le_testNorm K f y)) hb⟩
  rw [testNorm_signed_sup K x, testNorm_signed_sup K y,
    Real.mul_iSup_of_nonneg ha, Real.mul_iSup_of_nonneg hb, ciSup_add hba]
  apply ciSup_le
  intro f
  rw [add_ciSup hbb]
  exact ciSup_le (h f)

namespace TreeCalculus

theorem paired_finite_inequality {r : Bool} {k : QuadraticKind} {D : Set Node}
    (hD : Initial D) (hroot : [] ∈ D)
    (x y : TreeCoordinate r →₀ ℝ)
    (hx : ∀ s, x s ≠ 0 → s.val ∈ D) (hy : ∀ s, s.val ∈ D → y s = 0)
    {a θ t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (ht : 0 ≤ t) (hsquare : a^2 + θ^2 ≤ 1) :
    a * testNorm (treeTestFamily r k) x + (t * θ / 2) * testNorm (treeTestFamily r k) y ≤
      (testNorm (treeTestFamily r k) (x + t • y) + testNorm (treeTestFamily r k) (x - t • y)) / 2 := by
  apply testNorm_weighted_sup _ x y ha (by positivity)
  exact paired_finite_test_bound hD hroot x y hx hy ha ha1 hθ hθ1 hsquare

end TreeCalculus


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.FiniteHeads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section CompletedHeads
open scoped Classical
variable {I : Type*}

@[simp] lemma norm_coordinateVector (K : TestFamily I) (i : I) :
    ‖coordinateVector K i‖ = 1 := by
  simp only [coordinateVector, UniformSpace.Completion.norm_coe, norm_test_single]

lemma finiteHead_eq_sum (B : Finset I) (x : I →₀ ℝ) :
    Finsupp.filter (fun i => i ∈ B) x = ∑ i ∈ B, x i • Finsupp.single i 1 := by
  ext j
  simp only [Finsupp.filter_apply
    ]
  by_cases hj : j ∈ B <;> simp [Finsupp.single_apply, hj, eq_comm]

lemma completedHead_coe (K : TestFamily I) (B : Finset I) (x : TestVector K) :
    completedHead K B (x : TestCompletion K) =
      ((testVectorEquiv K).symm (Finsupp.filter (fun i => i ∈ B) (testVectorEquiv K x)) : TestCompletion K) := by
  rw [finiteHead_eq_sum]
  simp only [map_sum, map_smul]
  change completedHead K B (x : TestCompletion K) =
    (UniformSpace.Completion.toComplL : TestVector K →L[ℝ] TestCompletion K) (∑ i ∈ B, (testVectorEquiv K x) i • (testVectorEquiv K).symm (Finsupp.single i 1))
  simp only [map_sum, map_smul, completedHead_apply, coordinateFunctional_coe, coordinateVector]
  rfl

lemma mem_coordinateTail (K : TestFamily I) (B : Finset I) (x : TestCompletion K) :
    x ∈ coordinateTail K B ↔ ∀ i ∈ B, coordinateFunctional K i x = 0 := by
  change (headCoordinates K B x = 0) ↔ _
  simp only [headCoordinates, ContinuousLinearMap.pi_apply, funext_iff, Pi.zero_apply, Subtype.forall]

lemma coordinateTail_closed (K : TestFamily I) (B : Finset I) :
    IsClosed (coordinateTail K B : Set (TestCompletion K)) :=
  (headCoordinates K B).isClosed_ker

lemma completedTail_eq_self (K : TestFamily I) (B : Finset I) (x : TestCompletion K)
    (hx : x ∈ coordinateTail K B) : completedTail K B x = x := by
  rw [mem_coordinateTail] at hx
  rw [completedTail_apply, completedHead_apply]
  have hz : (∑ i ∈ B, coordinateFunctional K i x • coordinateVector K i) = 0 :=
    Finset.sum_eq_zero (fun i hi => by rw [hx i hi, zero_smul])
  rw [hz, sub_zero]

lemma completedTail_coe (K : TestFamily I) (B : Finset I) (x : TestVector K) :
    completedTail K B (x : TestCompletion K) =
      ((testVectorEquiv K).symm ((testVectorEquiv K x) - Finsupp.filter (fun i => i ∈ B) (testVectorEquiv K x)) : TestCompletion K) := by
  simp only [completedTail_apply, completedHead_coe, map_sub, LinearEquiv.symm_apply_apply,
    UniformSpace.Completion.coe_sub]

/-- Density transfer with a continuous tail projection. -/
lemma completion_norm_pair_bound (K : TestFamily I)
    (P : TestCompletion K →L[ℝ] TestCompletion K) (x : TestVector K) (a b t : ℝ)
    (h : ∀ w : TestVector K, a * ‖x‖ + b * ‖P (w : TestCompletion K)‖ ≤
      (‖(x : TestCompletion K) + t • P (w : TestCompletion K)‖ +
        ‖(x : TestCompletion K) - t • P (w : TestCompletion K)‖) / 2)
    (z : TestCompletion K) :
    a * ‖x‖ + b * ‖P z‖ ≤
      (‖(x : TestCompletion K) + t • P z‖ + ‖(x : TestCompletion K) - t • P z‖) / 2 := by
  have hc := P.continuous
  have hc1 : Continuous (fun z : TestCompletion K => a * ‖x‖ + b * ‖P z‖) :=
    continuous_const.add (continuous_const.mul hc.norm)
  have hc2 : Continuous (fun z : TestCompletion K =>
      (‖(x : TestCompletion K) + t • P z‖ + ‖(x : TestCompletion K) - t • P z‖) / 2) :=
    ((continuous_const.add (hc.const_smul t)).norm.add
      (continuous_const.sub (hc.const_smul t)).norm).div_const 2
  exact UniformSpace.Completion.induction_on z (isClosed_le hc1 hc2) h

end CompletedHeads

namespace TreeCalculus
open scoped Classical

lemma root_mem_initialHull {r : Bool} (x : TreeCoordinate r →₀ ℝ) :
    [] ∈ initialHull x := Finset.mem_insert_self _ _

lemma support_mem_initialHull {r : Bool} (x : TreeCoordinate r →₀ ℝ) (s : TreeCoordinate r)
    (hs : x s ≠ 0) : s.val ∈ initialHull x := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_biUnion.mpr
  exact ⟨s, Finsupp.mem_support_iff.mpr hs, by simp⟩

lemma initialHull_initial {r : Bool} (x : TreeCoordinate r →₀ ℝ) :
    Initial (initialHull x : Set Node) := by
  intro s u hs hus
  change s ∈ initialHull x at hs
  rw [initialHull, Finset.mem_insert] at hs
  rcases hs with rfl | hs
  · have hu : u = [] := List.prefix_nil.mp hus
    subst u
    exact root_mem_initialHull x
  · obtain ⟨i, hi, his⟩ := Finset.mem_biUnion.mp hs
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨i, hi, ?_⟩
    exact List.mem_toFinset.mpr ((List.mem_inits u i.val).mpr (hus.trans ((List.mem_inits s i.val).mp (List.mem_toFinset.mp his))))

lemma paired_vector_inequality {r : Bool} {k : QuadraticKind} {D : Set Node}
    (hD : Initial D) (hroot : [] ∈ D)
    (x y : TestVector (treeTestFamily r k))
    (hx : ∀ s, (testVectorEquiv _ x) s ≠ 0 → s.val ∈ D)
    (hy : ∀ s, s.val ∈ D → (testVectorEquiv _ y) s = 0)
    {a θ t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (ht : 0 ≤ t) (hsquare : a^2 + θ^2 ≤ 1) :
    a * ‖x‖ + (t * θ / 2) * ‖y‖ ≤ (‖x + t • y‖ + ‖x - t • y‖) / 2 := by
  simp only [norm_testVector_equiv, map_add, map_sub, map_smul]
  exact paired_finite_inequality hD hroot _ _ hx hy ha ha1 hθ hθ1 ht hsquare

lemma paired_projected_inequality {r : Bool} {k : QuadraticKind} {D : Finset Node}
    (hD : Initial (D : Set Node)) (hroot : [] ∈ D)
    (x w : TestVector (treeTestFamily r k))
    (hx : ∀ s, (testVectorEquiv _ x) s ≠ 0 → s.val ∈ D)
    {a θ t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (ht : 0 ≤ t) (hsquare : a^2 + θ^2 ≤ 1) :
    a * ‖x‖ + (t * θ / 2) * ‖completedTail (treeTestFamily r k) (coordinateHead r D) w‖ ≤
      (‖(x : TestCompletion (treeTestFamily r k)) +
          t • completedTail (treeTestFamily r k) (coordinateHead r D) w‖ +
        ‖(x : TestCompletion (treeTestFamily r k)) -
          t • completedTail (treeTestFamily r k) (coordinateHead r D) w‖) / 2 := by
  rw [completedTail_coe]
  rw [← UniformSpace.Completion.coe_smul, ← UniformSpace.Completion.coe_add,
    ← UniformSpace.Completion.coe_sub]
  simp only [UniformSpace.Completion.norm_coe]
  apply paired_vector_inequality hD hroot _ _ hx ?_ ha ha1 hθ hθ1 ht hsquare
  intro s hs
  simp only [LinearEquiv.apply_symm_apply, Finsupp.sub_apply, Finsupp.filter_apply]
  rw [ite_eq_left ((mem_coordinateHead r D s).mpr hs), sub_self]

/-- The paired inequality on the actual completion. Finite tails are obtained
    by applying a continuous finite-coordinate tail projection to dense arrays. -/
theorem paired_completed_inequality {r : Bool} {k : QuadraticKind} {D : Finset Node}
    (hD : Initial (D : Set Node)) (hroot : [] ∈ D)
    (x : TestVector (treeTestFamily r k)) (y : TestCompletion (treeTestFamily r k))
    (hx : ∀ s, (testVectorEquiv _ x) s ≠ 0 → s.val ∈ D)
    (hy : y ∈ coordinateTail (treeTestFamily r k) (coordinateHead r D))
    {a θ t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (ht : 0 ≤ t) (hsquare : a^2 + θ^2 ≤ 1) :
    a * ‖x‖ + (t * θ / 2) * ‖y‖ ≤
      (‖(x : TestCompletion (treeTestFamily r k)) + t • y‖ +
        ‖(x : TestCompletion (treeTestFamily r k)) - t • y‖) / 2 := by
  have h := completion_norm_pair_bound (treeTestFamily r k)
    (completedTail (treeTestFamily r k) (coordinateHead r D)) x a (t*θ/2) t
    (fun w => paired_projected_inequality hD hroot x w hx ha ha1 hθ hθ1 ht hsquare) y
  simpa only [completedTail_eq_self _ _ y hy] using h

end TreeCalculus


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.Moduli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

lemma ereal_le_of_forall_pos_sub_le (a : ℝ) (b : EReal)
    (h : ∀ ε : ℝ, 0 < ε → ((a - ε : ℝ) : EReal) ≤ b) : (a : EReal) ≤ b := by
  cases b using EReal.rec with
  | bot => exact ((EReal.bot_lt_coe (a - 1)).not_ge (h 1 zero_lt_one)).elim
  | coe b => exact EReal.coe_le_coe_iff.mpr (le_of_forall_pos_sub_le (fun ε hε =>
      EReal.coe_le_coe_iff.mp (h ε hε)))
  | top => exact le_top

lemma averagedModulus_lower_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {t b : ℝ}
    (h : ∀ x : E, ‖x‖ = 1 → ∀ ε : ℝ, 0 < ε → ∃ F : ClosedFiniteCodim E,
      ∀ y : E, y ∈ F.space → 1 ≤ ‖y‖ →
        b - ε ≤ (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1) :
    (b : EReal) ≤ averagedModulus E t := by
  apply le_iInf
  intro x
  apply ereal_le_of_forall_pos_sub_le
  intro ε hε
  obtain ⟨F, hF⟩ := h x.val x.property ε hε
  apply le_iSup_of_le F
  apply le_iInf
  intro y
  exact EReal.coe_le_coe_iff.mpr (hF y.val y.property.1 y.property.2)

lemma midpoint_center_perturbation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x z y : E) (t : ℝ) :
    (‖z + t • y‖ + ‖z - t • y‖) / 2 ≤
      (‖x + t • y‖ + ‖x - t • y‖) / 2 + ‖z - x‖ := by
  have h1 := norm_sub_norm_le (z + t • y) (x + t • y)
  have h2 := norm_sub_norm_le (z - t • y) (x - t • y)
  have he1 : (z + t • y) - (x + t • y) = z - x := by abel
  have he2 : (z - t • y) - (x - t • y) = z - x := by abel
  rw [he1] at h1
  rw [he2] at h2
  linarith

lemma optimal_pair_parameters {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ a θ : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ θ ∧ θ ≤ 1/2 ∧ a^2 + θ^2 ≤ 1 ∧
      a + t * θ / 2 = Real.sqrt (1 + t^2/4) := by
  let d := Real.sqrt (4 + t^2)
  have hd : 0 < d := Real.sqrt_pos.2 (by positivity)
  have hd2 : d^2 = 4 + t^2 := Real.sq_sqrt (by positivity)
  have hdle : 2 ≤ d := by nlinarith
  refine ⟨2 / d, t / d, by positivity, (div_le_one hd).mpr hdle,
    by positivity, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hd).mpr
    nlinarith
  · have he : (2 / d)^2 + (t / d)^2 = 1 := by
      field_simp
      nlinarith
    exact he.le
  · have he : 2 / d + t * (t / d) / 2 = d / 2 := by
      field_simp
      nlinarith
    rw [he]
    have hs : (d / 2)^2 = 1 + t^2 / 4 := by nlinarith
    rw [← hs, Real.sqrt_sq (by positivity)]

namespace TreeCalculus
open scoped Classical

/-- Uniform quantitative tail estimate at every unit center, including centers
    in the completion. The finite codimensional space may depend on ε. -/
theorem four_completed_tail_bound {r : Bool} {k : QuadraticKind}
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (x : TestCompletion (treeTestFamily r k)) (hx : ‖x‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : ClosedFiniteCodim (TestCompletion (treeTestFamily r k)),
      ∀ y, y ∈ F.space → 1 ≤ ‖y‖ →
      Real.sqrt (1 + t^2/4) - 1 - ε ≤ (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 := by
  let K := treeTestFamily r k
  obtain ⟨a, θ, ha, ha1, hθ, hθ1, hsquare, he⟩ := optimal_pair_parameters ht ht1
  obtain ⟨w, hw⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x
    (show 0 < ε / 3 by positivity)
  have hw' : ‖(w : TestCompletion K) - x‖ < ε / 3 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hw
  let D := initialHull (testVectorEquiv K w)
  let B := coordinateHead r D
  refine ⟨⟨coordinateTail K B, coordinateTail_closed K B, inferInstance⟩, ?_⟩
  intro y hy hy1
  have hp := paired_completed_inequality (initialHull_initial _) (root_mem_initialHull _)
    w y (support_mem_initialHull _) hy ha ha1 hθ hθ1 ht.le hsquare
  have hnw : 1 - ε / 3 ≤ ‖w‖ := by
    have hn := norm_sub_norm_le x (w : TestCompletion K)
    rw [hx, UniformSpace.Completion.norm_coe, norm_sub_rev] at hn
    linarith
  have haw : a - ε / 3 ≤ a * ‖w‖ := by
    have hmul := mul_le_mul_of_nonneg_left hnw ha
    have hc : a * (ε / 3) ≤ ε / 3 := mul_le_of_le_one_left (by positivity) ha1
    nlinarith
  have hby : t * θ / 2 ≤ (t * θ / 2) * ‖y‖ := le_mul_of_one_le_right (by positivity) hy1
  have hperturb := midpoint_center_perturbation x (w : TestCompletion K) y t
  linarith

/-- The common lower bound, with each root convention and quadratic budget kept distinct. -/
theorem four_averaged_modulus (r : Bool) (k : QuadraticKind)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ((Real.sqrt (1 + t^2/4) - 1 : ℝ) : EReal) ≤
      averagedModulus (TestCompletion (treeTestFamily r k)) t := by
  apply averagedModulus_lower_bound
  intro x hx ε hε
  exact four_completed_tail_bound ht ht1 x hx hε

end TreeCalculus


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.WeakNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section WeakNullSequences
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeaklyNull.map {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {d : ℕ → E} (hd : WeaklyNull d) (L : E →L[ℝ] Y) : WeaklyNull (fun n => L (d n)) :=
  fun φ => hd (φ.comp L)

/-- Weak nullity really gives approximation in every closed finite-codimensional
    subspace; the finite-dimensional quotient step is proved explicitly. -/
lemma WeaklyNull.approximable {d : ℕ → E} (hd : WeaklyNull d) (F : ClosedFiniteCodim E)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ w : E, w ∈ F.space ∧ ‖d n - w‖ < ε := by
  let : IsClosed (F.space : Set E) := F.closed
  let : Module.Finite ℝ (E ⧸ F.space) := F.finiteCodim
  let e := (Module.finBasis ℝ (E ⧸ F.space)).equivFunL
  have hc : Tendsto (fun n => e (F.space.mkQL (d n))) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact hd ((ContinuousLinearMap.proj i).comp (e.toContinuousLinearMap.comp F.space.mkQL))
  have hq : Tendsto (fun n => F.space.mkQL (d n)) atTop (𝓝 0) := by
    have h := (e.symm.continuous.tendsto 0).comp hc
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply, map_zero] using h
  have hqn : Tendsto (fun n => ‖F.space.mkQL (d n)‖) atTop (𝓝 0) := by simpa using hq.norm
  have he := hqn.eventually_lt_const (show 0 < ε/2 by positivity)
  filter_upwards [he] with n hn
  obtain ⟨u, hu, hun⟩ := Submodule.Quotient.norm_mk_lt (F.space.mkQL (d n))
    (show 0 < ε/2 by positivity)
  refine ⟨d n - u, (Submodule.Quotient.eq F.space).mp hu.symm, ?_⟩
  have heq : d n - (d n - u) = u := by abel
  rw [heq]
  linarith

lemma hilbert_upper_eval_sq_sum {I : Type*} (v : I → E)
    (hv : ∀ (A : Finset I) (a : I → ℝ),
      ‖∑ n ∈ A, a n • v n‖ ≤ Real.sqrt (∑ n ∈ A, (a n)^2))
    (φ : E →L[ℝ] ℝ) (A : Finset I) :
    ∑ n ∈ A, φ (v n)^2 ≤ ‖φ‖^2 := by
  let S := ∑ n ∈ A, φ (v n)^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hscalar : φ (∑ n ∈ A, φ (v n) • v n) = S := by
    simp only [map_sum, map_smul, smul_eq_mul, S, pow_two]
  have hnorm := φ.le_opNorm (∑ n ∈ A, φ (v n) • v n)
  rw [hscalar, Real.norm_eq_abs, abs_of_nonneg hS] at hnorm
  have hprod : S ≤ ‖φ‖ * Real.sqrt S := hnorm.trans
    (mul_le_mul_of_nonneg_left (hv A (fun n => φ (v n))) (norm_nonneg φ))
  have hs : Real.sqrt S ≤ ‖φ‖ := by
    by_cases hzero : Real.sqrt S = 0
    · rw [hzero]; exact norm_nonneg _
    · have hpos : 0 < Real.sqrt S := lt_of_le_of_ne (Real.sqrt_nonneg S) (Ne.symm hzero)
      apply (mul_le_mul_iff_right₀ hpos).mp
      nlinarith [Real.sq_sqrt hS]
  nlinarith [Real.sq_sqrt hS, norm_nonneg φ, Real.sqrt_nonneg S]

lemma weaklyNull_of_hilbert_upper (v : ℕ → E)
    (hv : ∀ (A : Finset ℕ) (a : ℕ → ℝ),
      ‖∑ n ∈ A, a n • v n‖ ≤ Real.sqrt (∑ n ∈ A, (a n)^2)) : WeaklyNull v := by
  intro φ
  have hs : Summable (fun n => φ (v n)^2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) (hilbert_upper_eval_sq_sum v hv φ)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := hs.tendsto_atTop_zero.sqrt
  simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using h

lemma oneSidedModulus_nonneg (t : ℝ) : (0 : EReal) ≤ oneSidedModulus E t := by
  apply le_iInf
  intro x
  obtain ⟨φ, hφ, hxφ⟩ := exists_dual_vector'' ℝ x.val
  apply le_iSup_of_le (functionalKernel φ)
  apply le_iInf
  intro y
  have hφy : φ y.val = 0 := y.property.1
  have h := φ.le_of_opNorm_le hφ (x.val + t • y.val)
  rw [map_add, map_smul, hφy, smul_zero, add_zero, hxφ, x.property] at h
  simp only [Real.ringHom_apply, Real.norm_eq_abs, abs_one, one_mul] at h
  exact EReal.coe_le_coe_iff.mpr (by linarith)

lemma oneSided_sphere_tail {t γ : ℝ} (hγ : (γ : EReal) < oneSidedModulus E t)
    (x : E) (hx : ‖x‖ = 1) :
    ∃ F : ClosedFiniteCodim E, ∀ y : E, y ∈ F.space → ‖y‖ = 1 →
      1 + γ ≤ ‖x + t • y‖ := by
  have hxlt := hγ.trans_le (iInf_le _ (⟨x, hx⟩ : {x : E // ‖x‖ = 1}))
  obtain ⟨F, hF⟩ := lt_iSup_iff.mp hxlt
  refine ⟨F, ?_⟩
  intro y hy hyn
  have hylt := hF.trans_le (iInf_le _ (⟨y, hy, hyn⟩ : {y : E // y ∈ F.space ∧ ‖y‖ = 1}))
  have hreal := EReal.coe_lt_coe_iff.mp hylt
  linarith

end WeakNullSequences

section AUCRayGrowth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_bound_extends_to_rays (x : E) (hx : ‖x‖ = 1) (F : Submodule ℝ E)
    {t γ : ℝ} (hγ : 0 ≤ γ)
    (hsphere : ∀ y : E, y ∈ F → ‖y‖ = 1 → 1 + γ ≤ ‖x + t • y‖)
    (y : E) (hy : y ∈ F) (hy1 : 1 ≤ ‖y‖) :
    1 + γ ≤ ‖x + t • y‖ := by
  let a := ‖y‖⁻¹
  have hyn : 0 < ‖y‖ := lt_of_lt_of_le zero_lt_one hy1
  have ha : 0 < a := inv_pos.mpr hyn
  have ha1 : a ≤ 1 := by
    simpa only [a, one_div] using ((div_le_one hyn).mpr hy1 : 1 / ‖y‖ ≤ 1)
  have hay : ‖a • y‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg ha.le]
    exact inv_mul_cancel₀ (ne_of_gt hyn)
  have h := hsphere (a • y) (F.smul_mem a hy) hay
  have he : x + t • (a • y) = (1-a) • x + a • (x + t • y) := by module
  rw [he] at h
  have hn := norm_add_le ((1-a) • x) (a • (x + t • y))
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ha1),
    Real.norm_of_nonneg ha.le, hx, mul_one] at hn
  by_contra hh
  have hlong := lt_of_not_ge hh
  have hprod := mul_lt_mul_of_pos_left hlong ha
  have hγa : a * γ ≤ γ := mul_le_of_le_one_left hγ ha1
  nlinarith

lemma oneSided_wide_tail {t γ : ℝ} (ht : 0 < t) (hγ : 0 ≤ γ)
    (hδ : (γ : EReal) < oneSidedModulus E t) (p : E) (hp : 0 < ‖p‖) :
    ∃ F : ClosedFiniteCodim E, ∀ w : E, w ∈ F.space → t * ‖p‖ ≤ ‖w‖ →
      (1 + γ) * ‖p‖ ≤ ‖p + w‖ := by
  let x := ‖p‖⁻¹ • p
  have hx : ‖x‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
    exact inv_mul_cancel₀ (ne_of_gt hp)
  obtain ⟨F, hF⟩ := oneSided_sphere_tail hδ x hx
  refine ⟨F, ?_⟩
  intro w hw hwn
  let v := (t * ‖p‖)⁻¹ • w
  have hv : v ∈ F.space := F.space.smul_mem _ hw
  have hc : 0 < t * ‖p‖ := mul_pos ht hp
  have hvn : 1 ≤ ‖v‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), mul_comm, ← div_eq_mul_inv]
    exact (le_div_iff₀ hc).mpr (by simpa using hwn)
  have h := norm_bound_extends_to_rays x hx F.space hγ hF v hv hvn
  have hec : t * (t * ‖p‖)⁻¹ = ‖p‖⁻¹ := by
    field_simp
  have he : x + t • v = ‖p‖⁻¹ • (p + w) := by
    dsimp only [x, v]
    rw [smul_smul, hec, smul_add]
  rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le), mul_comm, ← div_eq_mul_inv] at h
  exact (le_div_iff₀ hp).mp h

/-- One weakly-null child sequence gives a definite AUC increase. -/
lemma oneSided_growth {t γ c : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hc : 0 < c)
    (hδ : (γ : EReal) < oneSidedModulus E t) (p : E) (hp : 0 < ‖p‖)
    (htp : t * ‖p‖ ≤ c/2) (d : ℕ → E) (hd : WeaklyNull d)
    (hdn : ∀ n, c ≤ ‖d n‖) :
    ∃ n, ‖p‖ + γ * ‖p‖ / 2 ≤ ‖p + d n‖ := by
  obtain ⟨F, hF⟩ := oneSided_wide_tail ht hγ.le hδ p hp
  have hε : 0 < min (c/2) (γ * ‖p‖ / 2) := lt_min (by positivity) (by positivity)
  obtain ⟨n, w, hw, he⟩ := (hd.approximable F hε).exists
  have hec : ‖d n - w‖ < c/2 := he.trans_le (min_le_left _ _)
  have heγ : ‖d n - w‖ < γ * ‖p‖ / 2 := he.trans_le (min_le_right _ _)
  have hwn : t * ‖p‖ ≤ ‖w‖ := by
    have h := norm_sub_norm_le (d n) w
    have hd' := hdn n
    linarith
  have hfw := hF w hw hwn
  have hpert := norm_sub_norm_le (p + w) (p + d n)
  have heq : (p + w) - (p + d n) = w - d n := by abel
  rw [heq, norm_sub_rev] at hpert
  exact ⟨n, by linarith⟩

end AUCRayGrowth

section BoundedTrees
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma exists_pos_real_lt_ereal {b : EReal} (hb : 0 < b) :
    ∃ γ : ℝ, 0 < γ ∧ (γ : EReal) < b := by
  cases b using EReal.rec with
  | bot => exact (not_lt_bot hb).elim
  | coe b =>
    have hb' : 0 < b := EReal.coe_lt_coe_iff.mp hb
    exact ⟨b/2, by positivity, EReal.coe_lt_coe_iff.mpr (by linarith)⟩
  | top => exact ⟨1, zero_lt_one, EReal.coe_lt_top 1⟩

/-- The bounded-tree obstruction for arbitrary finite heights. Weak nullity is tested against the whole dual; iteration of the positive per-step gain gives the contradiction. -/


theorem bounded_tree_modulus_eq_zero
    (p : (h : ℕ) → Tree h → E) {m M c : ℝ}
    (hm : 0 < m) (hmM : m ≤ M) (hc : 0 < c)
    (hbound : ∀ h, 1 ≤ h → ∀ s : Tree h, m ≤ ‖p h s‖ ∧ ‖p h s‖ ≤ M)
    (hweak : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h),
      WeaklyNull (fun n => p h (child s hs n) - p h s))
    (hinc : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h) (n : ℕ),
      c ≤ ‖p h (child s hs n) - p h s‖) :
    oneSidedModulus E (c / (2 * M)) = 0 := by
  apply le_antisymm ?_ (oneSidedModulus_nonneg _)
  by_contra hnot
  obtain ⟨γ, hγ, hγδ⟩ := exists_pos_real_lt_ereal (lt_of_not_ge hnot)
  have hM : 0 < M := hm.trans_le hmM
  have ht : 0 < c / (2 * M) := by positivity
  let a := γ * m / 2
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (M / a)
  let H := n + 1
  have hH : 1 ≤ H := Nat.le_add_left 1 n
  have hlarge : M < m + (H : ℝ) * a := by
    have hn' : M < (n : ℝ) * a := (div_lt_iff₀ ha).mp hn
    simp only [H, Nat.cast_add, Nat.cast_one]
    nlinarith
  have hpath : ∀ j : ℕ, j ≤ H → ∃ s : Tree H,
      s.val.length = j ∧ m + (j : ℝ) * a ≤ ‖p H s‖ := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact ⟨root H, rfl, by simpa using (hbound H hH (root H)).1⟩
    | succ j ih =>
      intro hj
      obtain ⟨s, hsl, hsn⟩ := ih (Nat.le_of_succ_le hj)
      have hs : s.val.length < H := by omega
      have hpb := hbound H hH s
      have hp : 0 < ‖p H s‖ := hm.trans_le hpb.1
      have htp : (c / (2 * M)) * ‖p H s‖ ≤ c/2 := by
        calc
          _ ≤ (c / (2 * M)) * M := mul_le_mul_of_nonneg_left hpb.2 ht.le
          _ = c/2 := by field_simp
      obtain ⟨i, hi⟩ := oneSided_growth ht hγ hc hγδ (p H s) hp htp
        (fun n => p H (child s hs n) - p H s) (hweak H hH s hs) (hinc H hH s hs)
      rw [add_sub_cancel] at hi
      refine ⟨child s hs i, by simp [hsl], ?_⟩
      have hgrowth : a ≤ γ * ‖p H s‖ / 2 := by
        dsimp [a]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpb.1 hγ.le) (by norm_num)
      rw [Nat.cast_succ]
      nlinarith
  obtain ⟨s, hs, hsn⟩ := hpath H le_rfl
  have hb := (hbound H hH s).2
  linarith

/-- Explicit equivalence constants are retained in the obstruction radius.
    Quantification over continuous linear copies is precisely quantification
    over equivalent norms via the identity linear equivalence. -/
theorem bounded_tree_renorming_obstruction
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (p : (h : ℕ) → Tree h → E) {m M c α β : ℝ}
    (hm : 0 < m) (hmM : m ≤ M) (hc : 0 < c)
    (hbound : ∀ h, 1 ≤ h → ∀ s : Tree h, m ≤ ‖p h s‖ ∧ ‖p h s‖ ≤ M)
    (hweak : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h),
      WeaklyNull (fun n => p h (child s hs n) - p h s))
    (hinc : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h) (n : ℕ),
      c ≤ ‖p h (child s hs n) - p h s‖)
    (e : E ≃L[ℝ] Y) (hα : 0 < α) (hαβ : α ≤ β)
    (he : ∀ x : E, α * ‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ β * ‖x‖) :
    oneSidedModulus Y (α * c / (2 * β * M)) = 0 := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hM : 0 < M := hm.trans_le hmM
  have hb' : ∀ h, 1 ≤ h → ∀ s : Tree h,
      α * m ≤ ‖e (p h s)‖ ∧ ‖e (p h s)‖ ≤ β * M := by
    intro h hh s
    exact ⟨(mul_le_mul_of_nonneg_left (hbound h hh s).1 hα.le).trans (he _).1,
      (he _).2.trans (mul_le_mul_of_nonneg_left (hbound h hh s).2 hβ.le)⟩
  have hw' : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h),
      WeaklyNull (fun n => e (p h (child s hs n)) - e (p h s)) := by
    intro h hh s hs
    have hw := (hweak h hh s hs).map e.toContinuousLinearMap
    change WeaklyNull (fun n => e (p h (child s hs n) - p h s)) at hw
    simpa only [map_sub] using hw
  have hi' : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h) (n : ℕ),
      α*c ≤ ‖e (p h (child s hs n)) - e (p h s)‖ := by
    intro h hh s hs n
    rw [← map_sub]
    exact (mul_le_mul_of_nonneg_left (hinc h hh s hs n) hα.le).trans (he _).1
  have hmM' : α*m ≤ β*M := (mul_le_mul_of_nonneg_left hmM hα.le).trans
    (mul_le_mul_of_nonneg_right hαβ hM.le)
  simpa only [mul_assoc] using bounded_tree_modulus_eq_zero (fun h s => e (p h s))
    (mul_pos hα hm) hmM' (mul_pos hα hc) hb' hw' hi'

end BoundedTrees

end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.TreeObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

namespace TreeCalculus
open scoped Classical

lemma finitePairing_nodeArray (r : Bool) (f : TreeCoordinate r → ℝ) (s : Node) :
    finitePairing f (nodeArray r s) = liftCoefficients r f s := by
  by_cases h : r = true ∨ s ≠ []
  · simp [nodeArray, h, finitePairing, liftCoefficients]
  · simp [nodeArray, h, liftCoefficients]

lemma finitePairing_pathArray (r : Bool) (f : TreeCoordinate r → ℝ) (s : Node) :
    finitePairing f (pathArray r s) = potential (liftCoefficients r f) s := by
  simp only [pathArray, map_list_sum, List.map_map, Function.comp_def,
    finitePairing_nodeArray, potential]

lemma pathArray_child (r : Bool) (s : Node) (n : ℕ) :
    pathArray r (s ++ [n]) = pathArray r s + nodeArray r (s ++ [n]) := by
  simp [pathArray, List.inits_append]

lemma pathArray_apply (r : Bool) (s : Node) (i : TreeCoordinate r) :
    pathArray r s i = if i.val <+: s then 1 else 0 := by
  rw [← finitePairing_single_test (pathArray r s) i, finitePairing_pathArray]
  trans potential (Pi.single i.val (1 : ℝ)) s
  · congr 1
    ext u
    by_cases hu : r = true ∨ u ≠ []
    · simp [liftCoefficients, hu, Pi.single_apply, Subtype.ext_iff]
    · have hn : u ≠ i.val := by rintro rfl; exact hu i.property
      simp [liftCoefficients, hu, hn]
  · exact potential_single i.val s

lemma testNorm_pathArray_le (r : Bool) (k : QuadraticKind) (s : Node) :
    testNorm (treeTestFamily r k) (pathArray r s) ≤ 1 := by
  apply ciSup_le
  intro f
  rw [finitePairing_pathArray]
  exact f.property.potential_bound s

lemma testNorm_pathArray (r : Bool) (k : QuadraticKind) (s : Node)
    (hs : r = true ∨ s ≠ []) : testNorm (treeTestFamily r k) (pathArray r s) = 1 := by
  apply le_antisymm (testNorm_pathArray_le r k s)
  have h := coordinate_le_testNorm (treeTestFamily r k) (pathArray r s) ⟨s,hs⟩
  simpa only [pathArray_apply, List.prefix_rfl, ite_true, abs_one] using h

lemma norm_treePath (r : Bool) (k : QuadraticKind) (s : Node) (hs : r = true ∨ s ≠ []) :
    ‖treePath r k s‖ = 1 := by
  simp only [treePath, UniformSpace.Completion.norm_coe, norm_testVector_equiv,
    LinearEquiv.apply_symm_apply]
  exact testNorm_pathArray r k s hs

lemma treePath_child_sub (r : Bool) (k : QuadraticKind) (s : Node) (n : ℕ) :
    treePath r k (s ++ [n]) - treePath r k s =
      coordinateVector (treeTestFamily r k) (childCoordinate r s n) := by
  simp only [treePath, pathArray_child, map_add, UniformSpace.Completion.coe_add,
    add_sub_cancel_left]
  simp only [nodeArray, show r = true ∨ s ++ [n] ≠ [] from Or.inr (by simp),
    dite_true, coordinateVector, childCoordinate]

lemma childNode_injective (s : Node) : Function.Injective (fun n : ℕ => s ++ [n]) := by
  intro n m h
  simpa using List.append_cancel_left h

lemma sibling_quadraticGroup (k : QuadraticKind) (s : Node) (A : Finset ℕ) :
    QuadraticGroup k (A.image (fun n => s ++ [n])) := by
  cases k with
  | sibling =>
    refine ⟨s, ?_⟩
    intro u hu
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨n, rfl⟩
  | antichain =>
    intro u hu v hv huv
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv
    constructor
    · intro hp
      apply huv
      exact hp.eq_of_length (by simp)
    · intro hp
      apply huv
      exact (hp.eq_of_length (by simp)).symm
  | global => trivial

lemma sibling_sq_sum_le {r : Bool} {k : QuadraticKind}
    (f : treeTestFamily r k) (s : Node) (A : Finset ℕ) :
    ∑ n ∈ A, f.val (childCoordinate r s n)^2 ≤ 1 := by
  have h := f.property.quadratic_budget (A.image (fun n => s ++ [n]))
    (sibling_quadraticGroup k s A)
  rw [Finset.sum_image (fun i hi j hj hij => childNode_injective s hij)] at h
  simpa only [← liftCoefficients_coord, childCoordinate] using h

lemma completedTestFunctional_vector {I : Type*} (K : TestFamily I) (f : K) (i : I) :
    completedTestFunctional K f (coordinateVector K i) = f.val i := by
  rw [coordinateVector, completedTestFunctional_coe]
  change finitePairing f.val (Finsupp.single i 1) = f.val i
  simp [finitePairing]

/-- Siblings have the asserted Hilbert upper estimate in each different model. -/
theorem sibling_hilbert_upper (r : Bool) (k : QuadraticKind) (s : Node)
    (A : Finset ℕ) (a : ℕ → ℝ) :
    ‖∑ n ∈ A, a n • coordinateVector (treeTestFamily r k) (childCoordinate r s n)‖ ≤
      Real.sqrt (∑ n ∈ A, (a n)^2) := by
  rw [completed_tests_norming]
  apply ciSup_le
  intro f
  simp only [map_sum, map_smul, completedTestFunctional_vector, smul_eq_mul]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq A a (fun n => f.val (childCoordinate r s n))
  have hf := sibling_sq_sum_le f s A
  have hS : 0 ≤ ∑ n ∈ A, (a n)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs : (∑ n ∈ A, a n * f.val (childCoordinate r s n))^2 ≤ ∑ n ∈ A, (a n)^2 :=
    hc.trans ((mul_le_mul_of_nonneg_left hf hS).trans_eq (mul_one _))
  nlinarith [Real.sq_sqrt hS, Real.sqrt_nonneg (∑ n ∈ A, (a n)^2)]

lemma siblings_weaklyNull (r : Bool) (k : QuadraticKind) (s : Node) :
    WeaklyNull (fun n => coordinateVector (treeTestFamily r k) (childCoordinate r s n)) :=
  weaklyNull_of_hilbert_upper _ (sibling_hilbert_upper r k s)

lemma fourBoundedTree_norm (r : Bool) (k : QuadraticKind) (h : ℕ) (s : Tree h) :
    ‖fourBoundedTree r k h s‖ = 1 := by
  exact norm_treePath r k _ (Or.inr (by simp))

lemma fourBoundedTree_difference (r : Bool) (k : QuadraticKind) (h : ℕ)
    (s : Tree h) (hs : s.val.length < h) (n : ℕ) :
    fourBoundedTree r k h (child s hs n) - fourBoundedTree r k h s =
      coordinateVector (treeTestFamily r k) (childCoordinate r ([0] ++ s.val) n) := by
  change treePath r k ([0] ++ (s.val ++ [n])) - treePath r k ([0] ++ s.val) = _
  rw [← List.append_assoc]
  exact treePath_child_sub r k _ n

/-- Exact zero radius for every equivalent norm represented on a continuous-linearly-equivalent real normed space. -/

theorem four_renorming_obstruction (r : Bool) (k : QuadraticKind)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : TestCompletion (treeTestFamily r k) ≃L[ℝ] Y) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β)
    (he : ∀ x, α * ‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ β * ‖x‖) :
    oneSidedModulus Y (α / (2 * β)) = 0 := by
  have hb : ∀ h, 1 ≤ h → ∀ s : Tree h,
      (1 : ℝ) ≤ ‖fourBoundedTree r k h s‖ ∧ ‖fourBoundedTree r k h s‖ ≤ 1 := by
    intro h hh s
    simp only [fourBoundedTree_norm, le_refl, and_self]
  have hw : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h),
      WeaklyNull (fun n => fourBoundedTree r k h (child s hs n) - fourBoundedTree r k h s) := by
    intro h hh s hs
    simp only [fourBoundedTree_difference]
    exact siblings_weaklyNull r k _
  have hi : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h) (n : ℕ),
      (1 : ℝ) ≤ ‖fourBoundedTree r k h (child s hs n) - fourBoundedTree r k h s‖ := by
    intro h hh s hs n
    simp only [fourBoundedTree_difference, norm_coordinateVector, le_refl]
  simpa only [mul_one] using bounded_tree_renorming_obstruction
    (fourBoundedTree r k) zero_lt_one le_rfl zero_lt_one hb hw hi e hα hαβ he

end TreeCalculus
section EquivalenceBounds
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma continuousEquiv_bounds (e : E ≃L[ℝ] Y) :
    ∃ α β : ℝ, 0 < α ∧ α ≤ β ∧ ∀ x, α * ‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ β * ‖x‖ := by
  let A := ‖e.symm.toContinuousLinearMap‖ + 1
  let B := ‖e.toContinuousLinearMap‖ + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by dsimp [A]; linarith [norm_nonneg e.symm.toContinuousLinearMap]
  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg e.toContinuousLinearMap]
  refine ⟨A⁻¹, B, inv_pos.mpr hA, (inv_le_one₀ hA).mpr hA1 |>.trans hB1, ?_⟩
  intro x
  constructor
  · have h := e.symm.toContinuousLinearMap.le_opNorm (e x)
    change ‖e.symm (e x)‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ at h
    rw [e.symm_apply_apply] at h
    have hu : ‖x‖ ≤ A * ‖e x‖ := by
      dsimp [A]
      nlinarith [norm_nonneg (e x)]
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hA), one_mul] using
      mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hA.le)
  · have h := e.toContinuousLinearMap.le_opNorm x
    change ‖e x‖ ≤ ‖e.toContinuousLinearMap‖ * ‖x‖ at h
    dsimp [B]
    nlinarith [norm_nonneg x]

end EquivalenceBounds

namespace TreeCalculus

theorem four_no_equivalent_AUC (r : Bool) (k : QuadraticKind)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : TestCompletion (treeTestFamily r k) ≃L[ℝ] Y) : ¬ IsAUC Y := by
  obtain ⟨α, β, hα, hαβ, he⟩ := continuousEquiv_bounds e
  have hβ : 0 < β := hα.trans_le hαβ
  intro hauc
  have hp := hauc (α/(2*β)) (by positivity)
  rw [four_renorming_obstruction r k e hα hαβ he] at hp
  exact lt_irrefl _ hp

end TreeCalculus

end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.RealModuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials
/-- Coercion commutes with a bounded real infimum. -/

lemma ereal_coe_ciInf {I : Type*} [Nonempty I] (f : I → ℝ)
    (hf : BddBelow (Set.range f)) :
    ((⨅ i,f i : ℝ) : EReal) = ⨅ i,(f i : EReal) := by
  have hl : ((⨅ i,f i : ℝ) : EReal) ≤ ⨅ i,(f i : EReal) := by
    apply le_iInf
    intro i
    exact EReal.coe_le_coe_iff.mpr (ciInf_le hf i)
  have hb : (⨅ i,(f i : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hl
  have ht : (⨅ i,(f i : EReal)) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (iInf_le (fun i => (f i : EReal)) (Classical.choice inferInstance))
  have he := EReal.coe_toReal ht hb
  apply le_antisymm hl
  rw [← he]
  apply EReal.coe_le_coe_iff.mpr
  apply le_ciInf
  intro i
  apply EReal.coe_le_coe_iff.mp
  rw [he]
  exact iInf_le _ i

lemma ereal_coe_ciSup {I : Type*} [Nonempty I] (f : I → ℝ)
    (hf : BddAbove (Set.range f)) :
    ((⨆ i,f i : ℝ) : EReal) = ⨆ i,(f i : EReal) := by
  have hu : (⨆ i,(f i : EReal)) ≤ ((⨆ i,f i : ℝ) : EReal) := by
    apply iSup_le
    intro i
    exact EReal.coe_le_coe_iff.mpr (le_ciSup hf i)
  have hb : (⨆ i,(f i : EReal)) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_iSup (fun i => (f i : EReal)) (Classical.choice inferInstance))
  have ht : (⨆ i,(f i : EReal)) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hu
  have he := EReal.coe_toReal ht hb
  apply le_antisymm _ hu
  rw [← he]
  apply EReal.coe_le_coe_iff.mpr
  apply ciSup_le
  intro i
  apply EReal.coe_le_coe_iff.mp
  rw [he]
  exact le_iSup (fun i => (f i : EReal)) i

lemma ereal_coe_modulus_game {X F : Type*} {Y : F → Type*}
    [Nonempty X] [Nonempty F] [∀ f,Nonempty (Y f)]
    (v : X → (f : F) → Y f → ℝ) {a b : ℝ}
    (hl : ∀ x f y,a ≤ v x f y) (hu : ∀ x f,∃ y,v x f y ≤ b) :
    ((⨅ x,⨆ f,⨅ y,v x f y : ℝ) : EReal) =
      ⨅ x,⨆ f,⨅ y,(v x f y : EReal) := by
  have hb x f : BddBelow (Set.range (v x f)) := ⟨a,by rintro _ ⟨y,rfl⟩; exact hl x f y⟩
  have hlo x f : a ≤ ⨅ y,v x f y := le_ciInf (hl x f)
  have hup x f : (⨅ y,v x f y) ≤ b := by
    obtain ⟨y,hy⟩ := hu x f
    exact (ciInf_le (hb x f) y).trans hy
  have hsup x : BddAbove (Set.range (fun f => ⨅ y,v x f y)) :=
    ⟨b,by rintro _ ⟨f,rfl⟩; exact hup x f⟩
  have hmid x : a ≤ ⨆ f,⨅ y,v x f y :=
    (hlo x (Classical.choice inferInstance)).trans (le_ciSup (hsup x) _)
  rw [ereal_coe_ciInf _ ⟨a,by rintro _ ⟨x,rfl⟩; exact hmid x⟩]
  congr 1
  funext x
  rw [ereal_coe_ciSup _ (hsup x)]
  congr 1
  funext f
  exact ereal_coe_ciInf _ (hb x f)

section RealModuli
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma ClosedFiniteCodim.unit_exists (hinf : ¬Module.Finite ℝ E)
    (F : ClosedFiniteCodim E) : ∃ y : E,y ∈ F.space ∧ ‖y‖=1 := by
  have hbot : F.space ≠ ⊥ := by
    intro h
    apply hinf
    let := F.finiteCodim
    exact Module.Finite.of_injective F.space.mkQ
      (LinearMap.ker_eq_bot.mp ((Submodule.ker_mkQ _).trans h))
  obtain ⟨v,hv,hvn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine ⟨‖v‖⁻¹ • v,F.space.smul_mem _ hv,?_⟩
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvn)]

lemma unit_nonempty_of_infinite (hinf : ¬Module.Finite ℝ E) :
    Nonempty {x : E // ‖x‖=1} := by
  obtain ⟨x,_,hx⟩ := (Classical.choice (inferInstance : Nonempty (ClosedFiniteCodim E))).unit_exists E hinf
  exact ⟨⟨x,hx⟩⟩

lemma unit_perturbation_bound {x y : E} (hx : ‖x‖=1) (hy : ‖y‖=1) (t : ℝ) :
    ‖x+t • y‖ ≤ 1+|t| ∧ ‖x-t • y‖ ≤ 1+|t| := by
  constructor
  · simpa only [hx,hy,norm_smul,Real.norm_eq_abs,mul_one] using norm_add_le x (t • y)
  · simpa only [hx,hy,norm_smul,Real.norm_eq_abs,mul_one] using norm_sub_le x (t • y)

lemma averagedModulusReal_coe (hinf : ¬Module.Finite ℝ E) (t : ℝ) :
    (averagedModulusReal E t : EReal)=averagedModulus E t := by
  let := unit_nonempty_of_infinite E hinf
  have (F : ClosedFiniteCodim E) : Nonempty {y : E // y ∈ F.space ∧ 1≤‖y‖} := by
    obtain ⟨y,hy,hyn⟩ := F.unit_exists E hinf
    exact ⟨⟨y,hy,hyn.ge⟩⟩
  apply ereal_coe_modulus_game (a := -1) (b := |t|)
  · intro x F y
    linarith [norm_nonneg (x.val+t • y.val),norm_nonneg (x.val-t • y.val)]
  · intro x F
    obtain ⟨y,hy,hyn⟩ := F.unit_exists E hinf
    refine ⟨⟨y,hy,hyn.ge⟩,?_⟩
    have hh := unit_perturbation_bound E x.property hyn t
    dsimp
    linarith [hh.1,hh.2]

lemma oneSidedModulus_eq_top_of_finite [Module.Finite ℝ E] (t : ℝ) :
    oneSidedModulus E t=⊤ := by
  apply top_unique
  apply le_iInf
  intro x
  let F : ClosedFiniteCodim E := ⟨⊥,by simp,inferInstance⟩
  apply le_trans _ (le_iSup (fun F : ClosedFiniteCodim E =>
    ⨅ y : {y : E // y ∈ F.space ∧ ‖y‖=1},((‖x.val+t • y.val‖-1 : ℝ) : EReal)) F)
  have : IsEmpty {y : E // y ∈ F.space ∧ ‖y‖=1} := by
    constructor
    intro y
    have hy : y.val=0 := y.property.1
    simpa [hy] using y.property.2
  simp

lemma infiniteDimensional_of_not_isAUC (h : ¬IsAUC E) : ¬Module.Finite ℝ E := by
  intro hf
  let := hf
  apply h
  intro t ht
  rw [oneSidedModulus_eq_top_of_finite]
  exact EReal.coe_lt_top 0

end RealModuli
end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.EndpointTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials
section RealEndpointTransfer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma averagedModulusReal_lower (h : ¬IsAUC E) {a t : ℝ}
    (ha : (a : EReal)≤ averagedModulus E t) : a≤ averagedModulusReal E t := by
  apply EReal.coe_le_coe_iff.mp
  rwa [averagedModulusReal_coe E (infiniteDimensional_of_not_isAUC E h)]

end RealEndpointTransfer

namespace TreeCalculus

theorem four_averaged_modulus_real_oai (r : Bool) (k : QuadraticKind)
    {t : ℝ} (ht : 0< t) (ht1 : t<1) :
    Real.sqrt (1+t^2/4)-1≤ averagedModulusReal (TestCompletion (treeTestFamily r k)) t :=
  averagedModulusReal_lower (four_no_equivalent_AUC r k (.refl ℝ _)) (four_averaged_modulus r k ht ht1)

end TreeCalculus

end BoundedTreePotentials


end

end OAI
end

theorem solution : type_of% @OAI.BoundedTreePotentials.TreeCalculus.four_averaged_modulus_real_oai := @OAI.BoundedTreePotentials.TreeCalculus.four_averaged_modulus_real_oai
