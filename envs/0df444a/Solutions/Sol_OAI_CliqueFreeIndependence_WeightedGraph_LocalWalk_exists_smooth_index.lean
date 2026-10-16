-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.exists_smooth_index
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:30:18.515828+00:00
-- url     : https://prove2.me/submissions/20fbc779-8147-473b-9e7c-4e62d069d5a5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/WalkEntropy.lean:L341-L382
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.exists_smooth_index. The node keeps its source
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
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteEntropy_entropy_ge_neg_log_of_density
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteEntropy_entropy_mix_gap
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteEntropy_entropy_supported_concentration
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteEntropy_partial_entropy_le
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteEntropy_relTerm_nonneg
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteKernel_exists_smoothed_row_distance
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteKernel_leakage_mul_le
import Theorems.Thm_OAI_CliqueFreeIndependence_Numerical_log_bounds
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_LocalWalk_incoming_good_le
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_LocalWalk_transition_reversible
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_LocalWalk_transition_stochastic
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_reach_bad_cross

-- ---- from OAI.Combinatorics.CliqueFree.Numerical ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace Numerical

lemma threshold_pos {x : ℝ} (hx : 0 < x) : 0 < threshold x :=
  one_div_pos.2 (mul_pos (Real.exp_pos x) (pow_pos hx 6))

lemma leakage_factor {x : ℝ} (hx : 0 < x) :
    x ^ 2 * threshold x * Real.exp x = 1 / x ^ 4 := by
  unfold threshold
  field_simp [hx.ne', (Real.exp_pos x).ne']

lemma ceil_bounds {x : ℝ} (hx : 32 ≤ x) :
    0 < ⌈x⌉₊ ∧ x ≤ (⌈x⌉₊ : ℝ) ∧ (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  have hl := Nat.le_ceil x
  have hu := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
  refine ⟨?_, hl, by linarith⟩
  have : (0 : ℝ) < (⌈x⌉₊ : ℝ) := by linarith
  exact_mod_cast this

end Numerical

end CliqueFreeIndependence

open Filter
namespace CliqueFreeIndependence.Numerical

end CliqueFreeIndependence.Numerical

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.WeightedGraph ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

lemma crossMass_factor (G : SimpleGraph V) (w : V → ℝ) (A B : Finset V) :
    crossMass G w A B = ∑ u ∈ A, w u * mass w (B ∩ neighbors G u) := by
  classical
  unfold crossMass mass
  apply sum_congr rfl
  intro u _
  rw [← filter_mem_eq_inter]
  simp only [sum_filter, mem_neighbors, mul_sum, mul_ite, mul_zero]

lemma commonMass_comm (G : SimpleGraph V) (w : V → ℝ) (u v : V) :
    commonMass G w u v = commonMass G w v u := by
  classical
  simp [commonMass, inter_comm]

lemma triangleMass_eq_sum (G : SimpleGraph V) (w : V → ℝ) :
    6 * triangleMass G w = ∑ u, w u * triangleAt G w u := by
  unfold triangleMass
  ring

lemma crossMass_neighbors (G : SimpleGraph V) (w : V → ℝ)
    (A : Finset V) (v : V) :
    crossMass G w A (neighbors G v) = ∑ u ∈ A, w u * commonMass G w u v := by
  rw [crossMass_factor]
  simp only [commonMass, inter_comm]

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

lemma divergence_nonneg {p q : I → ℝ} (hp : IsProb p) (hq : IsProb q)
    (hs : ∀ i, 0 < p i → 0 < q i) : 0 ≤ divergence p q := by
  have h := sum_nonneg (s := univ) fun i _ ↦ relTerm_nonneg (hp.1 i) (hq.1 i) (hs i)
  simpa [divergence, sum_add_distrib, sum_sub_distrib, hp.2, hq.2] using h

variable {J : Type v} [Fintype J]

/-- Mixing finitely many probability vectors. -/
lemma mix_isProb {a : J → ℝ} {p : J → I → ℝ} (ha : IsProb a)
    (hp : ∀ j, IsProb (p j)) : IsProb (fun i ↦ ∑ j, a j * p j i) := by
  refine ⟨fun i ↦ sum_nonneg fun j _ ↦ mul_nonneg (ha.1 j) ((hp j).1 i), ?_⟩
  rw [sum_comm]
  simp_rw [← mul_sum, fun j ↦ (hp j).2, mul_one]
  exact ha.2

omit [Fintype I] in
lemma mix_support {a : J → ℝ} {p : J → I → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hp : ∀ j i, 0 ≤ p j i) {j : J} (hj : 0 < a j) {i : I} (hi : 0 < p j i) :
    0 < ∑ k, a k * p k i := by
  classical
  exact (mul_pos hj hi).trans_le (single_le_sum
    (fun k _ ↦ mul_nonneg (ha k) (hp k i)) (mem_univ j))

lemma prob_sum_on {p : I → ℝ} (hp : IsProb p) (D : Finset I)
    (hs : ∀ i, i ∉ D → p i = 0) : ∑ i ∈ D, p i = 1 := by
  rw [← hp.2]
  exact sum_subset (subset_univ _) (fun i _ hi ↦ hs i hi)

lemma entropy_sum_on {w p : I → ℝ} (D : Finset I)
    (hs : ∀ i, i ∉ D → p i = 0) : entropy w p = ∑ i ∈ D, p i * Real.log (w i / p i) := by
  symm
  apply sum_subset (subset_univ _)
  intro i _ hi
  rw [hs i hi, zero_mul]

lemma entropy_supported_le_log (D : Finset I) {w p : I → ℝ}
    (hw : ∀ i ∈ D, 0 < w i) (hp : IsProb p)
    (hs : ∀ i, i ∉ D → p i = 0) {m : ℝ} (hm : 0 < m) (hwm : ∑ i ∈ D, w i ≤ m) :
    entropy w p ≤ Real.log m := by
  have h := partial_entropy_le D hw (fun i _ ↦ hp.1 i) hm hwm
  simpa only [prob_sum_on hp D hs, div_one, one_mul, ← entropy_sum_on D hs] using h

end FiniteEntropy

end CliqueFreeIndependence

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.EdgeState ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance] OAI.CliqueFreeIndependence.WeightedGraph.edgeStateDecEq
namespace EdgeState
variable {G : SimpleGraph V}
lemma sum_eq (f : V → V → ℝ) :
    (∑ e : EdgeState G, f e.src e.dst) = ∑ u, ∑ v ∈ neighbors G u, f u v := by
  classical
  change (∑ e : {e : V × V // G.Adj e.1 e.2}, f e.val.1 e.val.2) = _
  rw [← Finset.sum_subtype (univ.filter fun e : V × V ↦ G.Adj e.1 e.2)
    (by simp) (fun e : V × V ↦ f e.1 e.2)]
  simp only [sum_filter, Fintype.sum_prod_type, neighbors]

lemma sum_fiber (u : V) (f : V → ℝ) :
    (∑ e : EdgeState G, if e.src = u then f e.dst else 0) = ∑ v ∈ neighbors G u, f v := by
  classical
  rw [sum_eq (fun a b ↦ if a = u then f b else 0)]
  simp

end EdgeState

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.Reach ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

lemma badSet_subset (G : SimpleGraph V) (w : V → ℝ) (S : V → Finset V)
    (b : ℝ) (v : V) : badSet G w S b v ⊆ neighbors G v := filter_subset _ _

lemma exceptionalConstant_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ exceptionalConstant C := by
  unfold exceptionalConstant
  positivity

end CliqueFreeIndependence.WeightedGraph

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

lemma stationary_of_reversible {π : I → ℝ} {P : Kernel I}
    (hP : Stochastic P) (hr : Reversible π P) : Stationary π P := by
  intro j
  calc
    _ = ∑ i, π j * P j i := sum_congr rfl fun i _ ↦ hr i j
    _ = π j := by rw [← mul_sum, (hP j).2, mul_one]

lemma stationary_lazy {π : I → ℝ} {P : Kernel I} (hP : Stationary π P) :
    Stationary π (lazy P) := by
  classical
  intro j
  change (∑ i, π i * (((if i = j then 1 else 0) + P i j) / 2)) = π j
  simp only [← mul_div_assoc, mul_add, ← sum_div, sum_add_distrib,
    mul_ite, mul_one, mul_zero]
  simp only [sum_ite_eq', mem_univ, ite_true]
  rw [hP j]
  ring

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

lemma smoothed_zero (P : Kernel I) : smoothed P 0 = P := by
  classical
  simp [smoothed]

lemma smoothed_succ (P : Kernel I) (j : ℕ) :
    smoothed P (j + 1) = lazy P * smoothed P j := by
  classical
  unfold smoothed
  rw [pow_succ', ← mul_assoc, (commute_lazy P).eq, mul_assoc]

lemma smoothed_succ_right (P : Kernel I) (j : ℕ) :
    smoothed P (j + 1) = smoothed P j * lazy P := by
  classical
  simp [smoothed, pow_succ, mul_assoc]

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

lemma stationary_average {π : I → ℝ} {Q : Kernel I} (hQ : Stationary π Q) (f : I → ℝ) :
    (∑ i, π i * ∑ j, Q i j * f j) = ∑ j, π j * f j := by
  simp_rw [mul_sum, ← mul_assoc]
  rw [sum_comm]
  simp_rw [← sum_mul]
  exact sum_congr rfl fun j _ ↦ by rw [hQ j]

lemma entropy_increment {π w : I → ℝ} (hw : ∀ i, 0 < w i)
    {Q K : Kernel I} (hQ : Stochastic Q) (hK : Stochastic K) (hs : Stationary π Q) :
    avgEntropy π w (Q * K) - avgEntropy π w K =
      ∑ i, π i * ∑ j, Q i j * divergence (K j) ((Q * K) i) := by
  have he (i : I) := entropy_mix_gap hw (hQ i) hK
  have he' : ∀ i, entropy w ((Q * K) i) - ∑ j, Q i j * entropy w (K j) =
      ∑ j, Q i j * divergence (K j) ((Q * K) i) := he
  simp_rw [← he', mul_sub, sum_sub_distrib]
  rw [stationary_average hs]
  rfl

lemma entropy_increment_nonneg {π w : I → ℝ} (hπ : IsProb π) (hw : ∀ i, 0 < w i)
    {Q K : Kernel I} (hQ : Stochastic Q) (hK : Stochastic K) (hs : Stationary π Q) :
    0 ≤ avgEntropy π w (Q * K) - avgEntropy π w K := by
  rw [entropy_increment hw hQ hK hs]
  apply sum_nonneg
  intro i _
  apply mul_nonneg (hπ.1 i)
  apply sum_nonneg
  intro j _
  rcases ((hQ i).1 j).eq_or_lt with hj | hj
  · simp [← hj]
  exact mul_nonneg hj.le (divergence_nonneg (hK j) (stochastic_mul hQ hK i)
    (fun k hk ↦ mix_support (hQ i).1 (fun z ↦ (hK z).1) hj hk))

lemma smoothed_entropy_mono {π w : I → ℝ} (hπ : IsProb π) (hw : ∀ i, 0 < w i)
    {P : Kernel I} (hP : Stochastic P) (hs : Stationary π P) :
    Monotone (fun j ↦ avgEntropy π w (smoothed P j)) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [smoothed_succ]
  exact sub_nonneg.1 (entropy_increment_nonneg hπ hw (stochastic_lazy hP)
    (stochastic_smoothed hP j) (stationary_lazy hs))

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

lemma rowMass_compl {K : Kernel I} (hK : Stochastic K) (i : I) (A : Finset I) :
    rowMass K i Aᶜ = 1 - rowMass K i A := by
  have h : rowMass K i A + rowMass K i Aᶜ = 1 := by
    rw [rowMass, rowMass, sum_add_sum_compl, (hK i).2]
  linarith

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

lemma fiber_mass (u : V) : (∑ e ∈ fiber G u, vertexWeight G w e) = neighborMass G w u := by
  classical
  simp only [fiber, sum_filter, vertexWeight, EdgeState.sum_fiber, neighborMass, mass]

lemma normalizer_eq : normalizer G w = 6 * triangleMass G w := by
  rw [normalizer, EdgeState.sum_eq (fun u v ↦ w u * w v * commonMass G w u v),
    triangleMass_eq_sum]
  simp only [triangleAt, mul_sum, mul_assoc]

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

lemma smoothed_supported (n : ℕ) (e f : EdgeState G) (h : f ∉ fiber G e.src) :
    smoothed (transition G w) n e f = 0 := by
  apply smoothed_fixed_src
  intro he
  apply h
  exact (mem_fiber G f e.src).2 he.symm

lemma smoothed_density (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v) (n : ℕ) :
    ∀ e f, smoothed (transition G w) n e f ≤ x * vertexWeight G w f := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  exact FiniteKernel.smoothed_density (transition_stochastic hw hc0) (transition_density hw hx hc) n

lemma entropy_bounds [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) (n : ℕ) (e : EdgeState G) :
    -Real.log x ≤ entropy (vertexWeight G w) (smoothed (transition G w) n e) ∧
      entropy (vertexWeight G w) (smoothed (transition G w) n e) ≤ x := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hp := stochastic_smoothed (transition_stochastic hw hc0) n e
  constructor
  · exact entropy_ge_neg_log_of_density (w := vertexWeight G w) (fun f ↦ hw f.dst) hp hx
      (smoothed_density hw hx hc n e)
  · have h := entropy_supported_le_log (w := vertexWeight G w) (fiber G e.src) (fun f _ ↦ hw f.dst) hp
      (smoothed_supported n e) (Real.exp_pos x) (by rw [fiber_mass]; exact hL e.src)
    simpa only [Real.log_exp] using h

end LocalWalk

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.WalkEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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
variable {G : SimpleGraph V} {w : V → ℝ}

lemma liftSet_subset_fiber (u : V) (A : Finset V) : liftSet (G := G) u A ⊆ fiber G u := by
  intro e he
  exact (mem_fiber G e u).2 ((mem_liftSet u A e).1 he).1

lemma sum_liftSet (u : V) (A : Finset V) (f : V → ℝ) :
    (∑ e ∈ liftSet (G := G) u A, f e.dst) = ∑ v ∈ A ∩ neighbors G u, f v := by
  rw [liftSet, sum_filter]
  have he : (∑ e : EdgeState G, if e.src = u ∧ e.dst ∈ A then f e.dst else 0) =
      ∑ e : EdgeState G, if e.src = u then (if e.dst ∈ A then f e.dst else 0) else 0 := by
    apply sum_congr rfl
    intro e _
    by_cases hs : e.src = u <;> by_cases hd : e.dst ∈ A <;> simp [hs, hd]
  rw [he, EdgeState.sum_fiber u (fun v ↦ if v ∈ A then f v else 0), ← sum_filter]
  congr 1
  ext v
  simp [and_comm]

lemma reach_leakage (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    {L t : ℝ} (hL : ∀ u, neighborMass G w u ≤ L) (ht : 0 ≤ t)
    (n : ℕ) (e : EdgeState G) :
    rowMass (smoothed (transition G w) n) e
      (liftSet (G := G) e.src (reach G w t e.dst n))ᶜ ≤ n * (x ^ 2 * t * L) := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hP := transition_stochastic hw hc0
  induction n with
  | zero =>
    simp only [smoothed_zero, Nat.cast_zero, zero_mul, reach]
    apply le_of_eq
    apply sum_eq_zero
    intro f hf
    have hf' := mem_compl.1 hf
    by_cases hs : e.src = f.src
    · have ha : ¬G.Adj e.dst f.dst := by
        intro h
        exact hf' ((mem_liftSet _ _ _).2 ⟨hs.symm, (mem_neighbors G _ _).2 h⟩)
      simp [transition, hs, ha]
    · exact transition_fixed_src e f hs
  | succ n ih =>
    rw [smoothed_succ_right]
    have h := leakage_mul_le (stochastic_smoothed hP n) (stochastic_lazy hP) e
      (liftSet (G := G) e.src (reach G w t e.dst n))
      (liftSet (G := G) e.src (reach G w t e.dst (n+1)))
    have hinc := incoming_good_le hw hx hc ht n e (reach G w t e.dst n)
    have hmass := mul_le_mul_of_nonneg_left (hL e.src) (mul_nonneg (sq_nonneg x) ht)
    simp only [reach] at h
    simp only [Nat.cast_add, Nat.cast_one]
    change rowMass (smoothed (transition G w) n * lazy (transition G w)) e
      (liftSet (G := G) e.src (enlarge G w t (reach G w t e.dst n)))ᶜ ≤ _
    calc
      _ ≤ _ := h
      _ ≤ n * (x ^ 2 * t * L) + x ^ 2 * t * L :=
        add_le_add ih (hinc.trans hmass)
      _ = _ := by ring

lemma law_rev (e : EdgeState G) : law G w e.rev = law G w e := by
  simp only [law, EdgeState.src_rev, EdgeState.dst_rev, commonMass_comm G w e.dst e.src]
  ring

lemma law_bad_sum (B : V → Finset V) (hB : ∀ v, B v ⊆ neighbors G v) :
    (∑ e : EdgeState G, if e.src ∈ B e.dst then law G w e else 0) =
      (∑ v, w v * crossMass G w (B v) (neighbors G v)) / normalizer G w := by
  have hr := EdgeState.revEquiv (G := G) |>.sum_comp
    (fun e : EdgeState G ↦ if e.src ∈ B e.dst then law G w e else 0)
  simp only [EdgeState.revEquiv, Equiv.coe_fn_mk, EdgeState.src_rev, EdgeState.dst_rev,
    law_rev] at hr
  rw [← hr]
  unfold law
  rw [EdgeState.sum_eq (fun u v ↦ if v ∈ B u then
    w u * w v * commonMass G w u v / normalizer G w else 0)]
  simp_rw [crossMass_neighbors, mul_sum, sum_div]
  apply sum_congr rfl
  intro v _
  rw [← sum_filter]
  have he : (neighbors G v).filter (fun u ↦ u ∈ B v) = B v :=
    filter_mem_eq_inter.trans (inter_eq_right.2 (hB v))
  rw [he]
  apply sum_congr rfl
  intro u _
  rw [commonMass_comm G w v u]
  ring

lemma law_bad_le [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v)
    (B : V → Finset V) (hB : ∀ v, B v ⊆ neighbors G v) {q : ℝ}
    (hb : ∀ v, crossMass G w (B v) (neighbors G v) ≤ q * triangleAt G w v) :
    (∑ e : EdgeState G, if e.src ∈ B e.dst then law G w e else 0) ≤ q := by
  rw [law_bad_sum B hB, div_le_iff₀ (normalizer_pos hw hc)]
  calc
    _ ≤ ∑ v, w v * (q * triangleAt G w v) :=
      sum_le_sum fun v _ ↦ mul_le_mul_of_nonneg_left (hb v) (hw v).le
    _ = q * normalizer G w := by
      rw [normalizer_eq, triangleMass_eq_sum, mul_sum]
      apply sum_congr rfl
      intro v _
      ring

lemma entropy_good_row (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (e : EdgeState G) {b : ℝ} (hb : 1 ≤ b)
    (he : e.src ∉ badSet G w (fun v ↦ reach G w t v n) b e.dst) :
    entropy (vertexWeight G w) (smoothed (transition G w) n e) ≤
      Real.log 2 + Real.log b + (n * (x ^ 2 * t * Real.exp x)) * x := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hP := transition_stochastic hw hc0
  have hsmall : mass w (reach G w t e.dst n ∩ neighbors G e.src) ≤ b := by
    by_contra! h
    exact he (mem_filter.2 ⟨(mem_neighbors G _ _).2 e.adj.symm, h⟩)
  have h := entropy_supported_concentration (w := vertexWeight G w)
    (fiber G e.src) (liftSet (G := G) e.src (reach G w t e.dst n))
    (liftSet_subset_fiber _ _) (fun f _ ↦ hw f.dst) (stochastic_smoothed hP n e)
    (smoothed_supported n e) hb (Real.exp_pos x)
    (by change (∑ f ∈ liftSet (G := G) e.src (reach G w t e.dst n), w f.dst) ≤ b
        rw [sum_liftSet]; exact hsmall)
    (by rw [fiber_mass]; exact hL _)
  rw [Real.log_exp] at h
  have hl := reach_leakage hw hx hc hL ht n e
  rw [rowMass_compl (stochastic_smoothed hP n)] at hl
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hl hx.le))

lemma averaged_entropy_bound [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) {b q : ℝ} (hb : 1 ≤ b)
    (hbad : (∑ e : EdgeState G,
      if e.src ∈ badSet G w (fun v ↦ reach G w t v n) b e.dst then law G w e else 0) ≤ q) :
    avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) n) ≤
      Real.log 2 + Real.log b + (n * (x ^ 2 * t * Real.exp x)) * x + q * x := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hmu := law_isProb hw hc0
  let A := Real.log 2 + Real.log b + (n * (x ^ 2 * t * Real.exp x)) * x
  have hA : 0 ≤ A := by
    dsimp [A]
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlb : 0 ≤ Real.log b := Real.log_nonneg hb
    positivity
  have hrow (e : EdgeState G) :
      entropy (vertexWeight G w) (smoothed (transition G w) n e) ≤
        A + if e.src ∈ badSet G w (fun v ↦ reach G w t v n) b e.dst then x else 0 := by
    split_ifs with he
    · exact (entropy_bounds hw hx hc hL n e).2.trans (by linarith)
    · simpa only [add_zero] using entropy_good_row hw hx hc hL ht n e hb he
  calc
    _ ≤ ∑ e, law G w e *
        (A + if e.src ∈ badSet G w (fun v ↦ reach G w t v n) b e.dst then x else 0) :=
      sum_le_sum fun e _ ↦ mul_le_mul_of_nonneg_left (hrow e) (hmu.1 e)
    _ = A + (∑ e : EdgeState G,
        if e.src ∈ badSet G w (fun v ↦ reach G w t v n) b e.dst then law G w e else 0) * x := by
      simp only [mul_add, sum_add_distrib, ← sum_mul, hmu.2, one_mul, mul_ite, mul_zero]
      rw [sum_mul]
      simp only [ite_mul, zero_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hbad hx.le)

lemma avg_entropy_lower [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) (n : ℕ) :
    -Real.log x ≤ avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) n) := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hmu := law_isProb hw hc0
  calc
    _ = (∑ e, law G w e) * (-Real.log x) := by rw [hmu.2, one_mul]
    _ = ∑ e, law G w e * (-Real.log x) := sum_mul _ _ _
    _ ≤ _ := sum_le_sum fun e _ ↦ mul_le_mul_of_nonneg_left
      (entropy_bounds hw hx hc hL n e).1 (hmu.1 e)

lemma avg_entropy_upper [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    {C x : ℝ} (hC : 0 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x)
    (n : ℕ) (hn : (n : ℝ) ≤ 2 * x) :
    avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) n) ≤
      entropyConstant C * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx0).trans_le (hc u v huv)
  have hbad := law_bad_le hw hc0
    (badSet G w (fun u ↦ reach G w (Numerical.threshold x) u n) (x ^ 8))
    (badSet_subset G w _ _) (reach_bad_cross G (fun u ↦ (hw u).le) hC hCross hx hL hc hn)
  have hb : (1 : ℝ) ≤ x ^ 8 := one_le_pow₀ hx1
  have h := averaged_entropy_bound hw hx0 hc hL (Numerical.threshold_pos hx0).le n hb hbad
  rw [Real.log_pow] at h
  have hleak : ((n : ℝ) * (x ^ 2 * Numerical.threshold x * Real.exp x)) * x ≤ 1 := by
    rw [Numerical.leakage_factor hx0]
    calc
      _ = (n : ℝ) / x ^ 3 := by field_simp [hx0.ne']
      _ ≤ (2 * x) / x ^ 3 := div_le_div_of_nonneg_right hn (pow_pos hx0 3).le
      _ = 2 / x ^ 2 := by field_simp [hx0.ne']
      _ ≤ 1 := (div_le_iff₀ (pow_pos hx0 2)).2 (by nlinarith)
  have hE := exceptionalConstant_nonneg hC
  have hq : (exceptionalConstant C / x ^ 4) * x ≤ exceptionalConstant C * Real.log x := by
    calc
      _ = exceptionalConstant C / x ^ 3 := by field_simp [hx0.ne']
      _ ≤ exceptionalConstant C := (div_le_iff₀ (pow_pos hx0 3)).2 (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hx1 (n := 3)) hE)
      _ ≤ _ := by nlinarith [(Numerical.log_bounds hx).1]
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
  have hl1 := (Numerical.log_bounds hx).1
  unfold entropyConstant
  norm_num only [Nat.cast_ofNat] at h
  linarith

/-- The `C`-dependent entropy smoothing bound. -/
lemma exists_smooth_index [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    {C x : ℝ} (hC : 1 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) :
    ∃ j < ⌈x⌉₊,
      avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) j) ≤
        entropyConstant C * Real.log x ∧
      rowDistance (G := G) (w := w) j ≤ smoothingConstant C * Real.sqrt (Real.log x / x) := by
  have hx0 : 0 < x := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx0).trans_le (hc u v huv)
  have hmu := law_isProb hw hc0
  have hP := transition_stochastic hw hc0
  have hs := stationary_of_reversible hP (transition_reversible hw hc0)
  have hceil := Numerical.ceil_bounds hx
  have hlow := avg_entropy_lower hw hx0 hc hL 0
  have hupp := avg_entropy_upper hw hC0 hCross hx hc hL ⌈x⌉₊ hceil.2.2
  have hD : avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) ⌈x⌉₊) -
      avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) 0) ≤
      (entropyConstant C + 1) * Real.log x := by linarith
  obtain ⟨j, hj, hdist⟩ := exists_smoothed_row_distance hmu (fun e ↦ hw e.dst) hP hs hceil.1 hD
  refine ⟨j, hj, ?_, ?_⟩
  · exact (smoothed_entropy_mono hmu (fun e ↦ hw e.dst) hP hs (Nat.le_of_lt hj)).trans hupp
  · have hA : 0 ≤ entropyConstant C + 1 := by
      have := exceptionalConstant_nonneg hC0
      unfold entropyConstant
      linarith
    have hlog : 0 ≤ Real.log x := ((Numerical.log_bounds hx).1.trans' (by norm_num))
    have href : rowDistance (G := G) (w := w) j ^ 2 ≤
        4 * ((entropyConstant C + 1) * Real.log x) / x := by
      exact hdist.trans (div_le_div_of_nonneg_left (by positivity) hx0 hceil.2.1)
    have hf : 0 ≤ Real.log x / x := div_nonneg hlog hx0.le
    have hsq : (smoothingConstant C * Real.sqrt (Real.log x / x)) ^ 2 =
        4 * ((entropyConstant C + 1) * Real.log x) / x := by
      rw [mul_pow, smoothingConstant, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hf]
      ring
    have hn : 0 ≤ smoothingConstant C * Real.sqrt (Real.log x / x) := by
      unfold smoothingConstant
      positivity
    nlinarith

end LocalWalk

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance 10000] edgeStateDecEq
open FiniteEntropy FiniteKernel


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.exists_smooth_index.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.exists_smooth_index.{u}
