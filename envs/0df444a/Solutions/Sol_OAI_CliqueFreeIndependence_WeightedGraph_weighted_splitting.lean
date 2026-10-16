-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.weighted_splitting
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:47:45.561986+00:00
-- url     : https://prove2.me/submissions/51da0c32-a0ea-476d-8da5-8e2c7e8864d4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/VertexSplitting.lean:L49-L86
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.weighted_splitting. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel
import Definitions.Def_OAI_Combinatorics_CliqueFree_LocalWalk
import Definitions.Def_OAI_Combinatorics_CliqueFree_WalkEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteCoupling
import Definitions.Def_OAI_Combinatorics_CliqueFree_VertexSplitting
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteKernel_reversed_entropy_tail
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteKernel_reversible_mul
import Theorems.Thm_OAI_CliqueFreeIndependence_Numerical_log_bounds
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_LocalWalk_exists_smooth_index
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_LocalWalk_transition_reversible
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_LocalWalk_transition_stochastic
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_Splitting_exists_graph

-- ---- from OAI.Combinatorics.CliqueFree.WeightedGraph ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

omit [Fintype V] in
lemma mass_nonneg {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A : Finset V) :
    0 ≤ mass w A := sum_nonneg fun v _ ↦ hw v

lemma commonMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u v : V) :
    0 ≤ commonMass G w u v := mass_nonneg hw _

lemma triangleAt_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u : V) :
    0 ≤ triangleAt G w u :=
  sum_nonneg fun v _ ↦ mul_nonneg (hw v) (commonMass_nonneg G hw u v)

lemma triangleMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    0 ≤ triangleMass G w := div_nonneg
      (sum_nonneg fun u _ ↦ mul_nonneg (hw u) (triangleAt_nonneg G hw u)) (by norm_num)

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.FiniteEntropy ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteEntropy

variable {I : Type u} [Fintype I]

variable {J : Type v} [Fintype J]

/-- Mixing finitely many probability vectors. -/
lemma mix_isProb {a : J → ℝ} {p : J → I → ℝ} (ha : IsProb a)
    (hp : ∀ j, IsProb (p j)) : IsProb (fun i ↦ ∑ j, a j * p j i) := by
  refine ⟨fun i ↦ sum_nonneg fun j _ ↦ mul_nonneg (ha.1 j) ((hp j).1 i), ?_⟩
  rw [sum_comm]
  simp_rw [← mul_sum, fun j ↦ (hp j).2, mul_one]
  exact ha.2

end FiniteEntropy

end CliqueFreeIndependence

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.FiniteKernel ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteKernel

open FiniteEntropy
variable {I : Type u} [Fintype I]

attribute [local instance] OAI.CliqueFreeIndependence.FiniteKernel.instDecidableEq_oAI
lemma stochastic_one : Stochastic (1 : Kernel I) := by
  classical
  intro i
  constructor
  · intro j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  · simp [Matrix.one_apply]

lemma stochastic_mul {P Q : Kernel I} (hP : Stochastic P) (hQ : Stochastic Q) :
    Stochastic (P * Q) := by
  intro i
  exact mix_isProb (hP i) hQ

lemma stochastic_pow {P : Kernel I} (hP : Stochastic P) (n : ℕ) : Stochastic (P ^ n) := by
  classical
  induction n with
  | zero => simpa using (stochastic_one (I := I))
  | succ n ih => simpa only [pow_succ] using stochastic_mul ih hP

lemma stochastic_lazy {P : Kernel I} (hP : Stochastic P) : Stochastic (lazy P) := by
  classical
  intro i
  constructor
  · intro j
    dsimp [lazy]
    have := (hP i).1 j
    split_ifs <;> positivity
  · change (∑ j, ((if i = j then (1 : ℝ) else 0) + P i j) / 2) = 1
    rw [← sum_div, sum_add_distrib]
    simp [(hP i).2]

lemma stochastic_smoothed {P : Kernel I} (hP : Stochastic P) (j : ℕ) :
    Stochastic (smoothed P j) := stochastic_mul hP (stochastic_pow (stochastic_lazy hP) j)

omit [Fintype I] in
lemma reversible_one (π : I → ℝ) : Reversible π (1 : Kernel I) := by
  classical
  intro i j
  by_cases h : i = j
  · subst j; rfl
  · simp [h, Ne.symm h]

lemma reversible_pow {π : I → ℝ} {P : Kernel I} (hP : Reversible π P) (n : ℕ) :
    Reversible π (P ^ n) := by
  classical
  induction n with
  | zero => simpa using reversible_one π
  | succ n ih =>
    rw [pow_succ]
    exact reversible_mul ih hP ((Commute.refl P).pow_left n)

omit [Fintype I] in
lemma reversible_lazy {π : I → ℝ} {P : Kernel I} (hP : Reversible π P) :
    Reversible π (lazy P) := by
  classical
  intro i j
  by_cases h : i = j
  · subst j; rfl
  · simp only [lazy, h, Ne.symm h, ite_false, zero_add]
    rw [← mul_div_assoc, ← mul_div_assoc, hP i j]

omit [Fintype I] in
lemma lazy_eq (P : Kernel I) : lazy P = (1 / 2 : ℝ) • (1 + P) := by
  classical
  ext i j
  simp [lazy, Matrix.one_apply, div_eq_mul_inv, mul_comm]

lemma commute_lazy (P : Kernel I) : Commute P (lazy P) := by
  classical
  rw [lazy_eq]
  show P * ((1 / 2 : ℝ) • (1 + P)) = ((1 / 2 : ℝ) • (1 + P)) * P
  simp [mul_add, add_mul]

lemma reversible_smoothed {π : I → ℝ} {P : Kernel I} (hP : Reversible π P) (j : ℕ) :
    Reversible π (smoothed P j) := by
  classical
  exact reversible_mul hP (reversible_pow (reversible_lazy hP) j)
    ((commute_lazy P).pow_right j)

lemma smoothed_density {P : Kernel I} (hP : Stochastic P) {b : I → ℝ}
    (hb : ∀ i j, P i j ≤ b j) (n : ℕ) : ∀ i j, smoothed P n i j ≤ b j := by
  classical
  intro i j
  unfold smoothed
  rw [((commute_lazy P).pow_right n).eq, Matrix.mul_apply]
  have hQ := stochastic_pow (stochastic_lazy hP) n
  calc
    _ ≤ ∑ k, (lazy P ^ n) i k * b j :=
      sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hb k j) ((hQ i).1 k)
    _ = b j := by rw [← sum_mul, (hQ i).2, one_mul]

variable {J : Type v}

omit [Fintype I] in
lemma preserves_one (label : I → J) : Preserves label (1 : Kernel I) := by
  intro i j hij
  have h : i ≠ j := fun h ↦ hij (congrArg label h)
  simp [h]

lemma preserves_mul {label : I → J} {P Q : Kernel I}
    (hP : Preserves label P) (hQ : Preserves label Q) : Preserves label (P * Q) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply sum_eq_zero
  intro k _
  by_cases hik : label i = label k
  · have hkj : label k ≠ label j := fun h ↦ hij (hik.trans h)
    rw [hQ k j hkj, mul_zero]
  · rw [hP i k hik, zero_mul]

lemma preserves_pow {label : I → J} {P : Kernel I} (hP : Preserves label P) (n : ℕ) :
    Preserves label (P ^ n) := by
  induction n with
  | zero => simpa using preserves_one label
  | succ n ih => simpa only [pow_succ] using preserves_mul ih hP

omit [Fintype I] in
lemma preserves_lazy {label : I → J} {P : Kernel I} (hP : Preserves label P) :
    Preserves label (lazy P) := by
  intro i j hij
  have h : i ≠ j := fun h ↦ hij (congrArg label h)
  simp [lazy, h, hP i j hij]

lemma preserves_smoothed {label : I → J} {P : Kernel I} (hP : Preserves label P) (n : ℕ) :
    Preserves label (smoothed P n) :=
  preserves_mul hP (preserves_pow (preserves_lazy hP) n)

end FiniteKernel

end CliqueFreeIndependence

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.LocalWalk ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace LocalWalk
open FiniteEntropy FiniteKernel
variable (G : SimpleGraph V) (w : V → ℝ)

variable {G w}
lemma normalizer_pos [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) : 0 < normalizer G w := by
  exact sum_pos (fun e _ ↦ mul_pos (mul_pos (hw _) (hw _)) (hc _ _ e.adj)) univ_nonempty

lemma law_isProb [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) : IsProb (law G w) := by
  have hZ := normalizer_pos hw hc
  constructor
  · intro e
    exact (div_pos (mul_pos (mul_pos (hw _) (hw _)) (hc _ _ e.adj)) hZ).le
  · unfold law
    rw [← sum_div]
    exact div_self hZ.ne'

lemma transition_fixed_src (e f : EdgeState G) (h : e.src ≠ f.src) :
    transition G w e f = 0 := by simp [transition, h]

lemma transition_density (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v) :
    ∀ e f, transition G w e f ≤ x * vertexWeight G w f := by
  classical
  intro e f
  have hc0 : 0 < commonMass G w e.src e.dst := (one_div_pos.2 hx).trans_le (hc _ _ e.adj)
  dsimp [transition, vertexWeight]
  split_ifs
  · apply (div_le_iff₀ hc0).2
    have h := (div_le_iff₀ hx).1 (hc _ _ e.adj)
    nlinarith [mul_le_mul_of_nonneg_left h (hw f.dst).le]
  all_goals exact (mul_pos hx (hw _)).le

lemma smoothed_fixed_src (n : ℕ) (e f : EdgeState G) (h : e.src ≠ f.src) :
    smoothed (transition G w) n e f = 0 :=
  preserves_smoothed (label := EdgeState.src) transition_fixed_src n e f h

lemma smoothed_density (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v) (n : ℕ) :
    ∀ e f, smoothed (transition G w) n e f ≤ x * vertexWeight G w f := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  exact FiniteKernel.smoothed_density (transition_stochastic hw hc0) (transition_density hw hx hc) n

end LocalWalk

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.VertexSplitting ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

lemma splitting_error_le {C x : ℝ} (hC : 1 ≤ C) (hx : 32 ≤ x) :
    6 * (smoothingConstant C * Real.sqrt (Real.log x / x)) +
    6 * ((entropyConstant C + 1) * Real.log x / (Real.sqrt x + Real.log x)) ≤
    splittingConstant C * (Real.log x / Real.sqrt x) := by
  have hx0 : 0 < x := by linarith
  have hl := (Numerical.log_bounds hx).1
  have hl0 : 0 ≤ Real.log x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hA : 0 ≤ entropyConstant C + 1 := by
    unfold entropyConstant exceptionalConstant
    positivity
  have hB : 0 ≤ smoothingConstant C := by unfold smoothingConstant; positivity
  have hslog : Real.sqrt (Real.log x) ≤ Real.log x := by
    have hh := Real.sq_sqrt hl0
    have hn := Real.sqrt_nonneg (Real.log x)
    nlinarith
  have h1 : Real.sqrt (Real.log x / x) ≤ Real.log x / Real.sqrt x := by
    rw [Real.sqrt_div hl0]
    exact div_le_div_of_nonneg_right hslog hs.le
  have h2 : (entropyConstant C + 1) * Real.log x / (Real.sqrt x + Real.log x) ≤
      (entropyConstant C + 1) * (Real.log x / Real.sqrt x) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_left (mul_nonneg hA hl0) hs (by linarith)
  unfold splittingConstant
  nlinarith [mul_le_mul_of_nonneg_left h1 hB]

/-- Weighted vertex splitting with explicit constants. -/
lemma weighted_splitting {G : SimpleGraph V} [Nonempty (EdgeState G)] {w : V → ℝ}
    (hw : ∀ u, 0 < w u) {C x : ℝ} (hC : 1 ≤ C) (hCross : CrossBound G w C)
    (hx : 32 ≤ x) (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) :
    ∃ H : SimpleGraph (EdgeState G), EdgeProjection H G EdgeState.src ∧
      (∀ z, neighborMass H (w ∘ EdgeState.src) z ≤ Real.exp (Real.sqrt x)) ∧
      (1 - splittingConstant C * (Real.log x / Real.sqrt x)) * triangleMass G w ≤
        triangleMass H (w ∘ EdgeState.src) := by
  open FiniteEntropy FiniteKernel LocalWalk in
  have hx0 : 0 < x := by linarith
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx0).trans_le (hc u v huv)
  obtain ⟨j,_,hH,hD⟩ := LocalWalk.exists_smooth_index hw hC hCross hx hc hL
  let K := FiniteKernel.smoothed (LocalWalk.transition G w) j
  have hP := LocalWalk.transition_stochastic hw hc0
  have hK := FiniteKernel.stochastic_smoothed hP j
  have hrev := FiniteKernel.reversible_smoothed (LocalWalk.transition_reversible hw hc0) j
  have htail := FiniteKernel.reversed_entropy_tail (LocalWalk.law_isProb hw hc0)
    (fun e : EdgeState G ↦ hw e.dst) hK hrev hx0 (LocalWalk.smoothed_density hw hx0 hc j)
    (a := Real.sqrt x)
  have hden : 0 < Real.sqrt x + Real.log x := by
    have hs := Real.sqrt_pos.2 hx0
    linarith [(Numerical.log_bounds hx).1]
  have hδ : (∑ e, LocalWalk.law G w e * ∑ y,
      if K y e < w e.dst * Real.exp (-Real.sqrt x) then K e y else 0) ≤
        (entropyConstant C + 1) * Real.log x / (Real.sqrt x + Real.log x) := by
    apply (le_div_iff₀ hden).2
    dsimp [K]
    change FiniteKernel.avgEntropy (LocalWalk.law G w) (fun e ↦ w e.dst)
      (FiniteKernel.smoothed (LocalWalk.transition G w) j) ≤ entropyConstant C * Real.log x at hH
    nlinarith only [htail,hH]
  obtain ⟨H,hproj,hneigh,htri⟩ := Splitting.exists_graph hw hc0 K hK
    (LocalWalk.smoothed_fixed_src j) hD hδ
  refine ⟨H,hproj,hneigh,?_⟩
  have hn := triangleMass_nonneg G (fun u ↦ (hw u).le)
  have he := splitting_error_le hC hx
  nlinarith [mul_le_mul_of_nonneg_right he hn]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance 10000] edgeStateDecEq


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.weighted_splitting.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.weighted_splitting.{u}
