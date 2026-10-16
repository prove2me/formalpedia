-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.reach_bad_cross
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:16:03.52889+00:00
-- url     : https://prove2.me/submissions/0a4914c2-4b12-4342-aa46-d2f5e52dc2a5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Reach.lean:L192-L216
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.reach_bad_cross. The node keeps its source
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
import Theorems.Thm_OAI_CliqueFreeIndependence_Numerical_growth_factor_le
import Theorems.Thm_OAI_CliqueFreeIndependence_Numerical_log_bounds
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_growth_le_twice

-- ---- from OAI.Combinatorics.CliqueFree.Numerical ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace Numerical

lemma exp_neg_le_inv_pow_seven {x : ℝ} (hx : 32 ≤ x) :
    Real.exp (-x) ≤ 1 / x ^ 7 := by
  have hx0 : 0 < x := by linarith
  calc
    _ ≤ Real.exp (-(7 * Real.log x)) := Real.exp_le_exp.2 (by linarith [(log_bounds hx).2])
    _ = _ := by
      have hp : Real.log (x ^ 7) = 7 * Real.log x := by simp only [Real.log_pow, Nat.cast_ofNat]
      rw [Real.exp_neg, ← hp, Real.exp_log (pow_pos hx0 7)]
      simp only [one_div]

lemma threshold_pos {x : ℝ} (hx : 0 < x) : 0 < threshold x :=
  one_div_pos.2 (mul_pos (Real.exp_pos x) (pow_pos hx 6))

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

omit [Fintype V] in
lemma mass_nonneg {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A : Finset V) :
    0 ≤ mass w A := sum_nonneg fun v _ ↦ hw v

omit [Fintype V] in
lemma mass_mono {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {A B : Finset V} (hAB : A ⊆ B) :
    mass w A ≤ mass w B := sum_le_sum_of_subset_of_nonneg hAB (fun v _ _ ↦ hw v)

omit [Fintype V] in
lemma crossMass_symm (G : SimpleGraph V) (w : V → ℝ) (A B : Finset V) :
    crossMass G w A B = crossMass G w B A := by
  classical
  unfold crossMass
  rw [sum_comm]
  simp_rw [G.adj_comm, mul_comm]

lemma crossMass_factor (G : SimpleGraph V) (w : V → ℝ) (A B : Finset V) :
    crossMass G w A B = ∑ u ∈ A, w u * mass w (B ∩ neighbors G u) := by
  classical
  unfold crossMass mass
  apply sum_congr rfl
  intro u _
  rw [← filter_mem_eq_inter]
  simp only [sum_filter, mem_neighbors, mul_sum, mul_ite, mul_zero]

lemma commonMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u v : V) :
    0 ≤ commonMass G w u v := mass_nonneg hw _

lemma neighborMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u : V) :
    0 ≤ neighborMass G w u := mass_nonneg hw _

lemma commonMass_le_neighborMass (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (u v : V) : commonMass G w u v ≤ neighborMass G w u := by
  classical
  exact mass_mono hw inter_subset_left

lemma triangleAt_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u : V) :
    0 ≤ triangleAt G w u :=
  sum_nonneg fun v _ ↦ mul_nonneg (hw v) (commonMass_nonneg G hw u v)

lemma neighborMass_ge_of_commonMass (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {τ : ℝ} (hc : ∀ u v, G.Adj u v → τ ≤ commonMass G w u v)
    {u : V} (hu : (neighbors G u).Nonempty) : τ ≤ neighborMass G w u := by
  rcases hu with ⟨v, hv⟩
  exact (hc u v (mem_neighbors G u v |>.1 hv)).trans (commonMass_le_neighborMass G hw u v)

lemma triangleAt_ge_of_commonMass (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {τ : ℝ} (hc : ∀ u v, G.Adj u v → τ ≤ commonMass G w u v)
    (u : V) : τ * neighborMass G w u ≤ triangleAt G w u := by
  calc
    _ = ∑ v ∈ neighbors G u, w v * τ := by rw [← sum_mul]; exact mul_comm _ _
    _ ≤ _ := sum_le_sum fun v hv ↦ mul_le_mul_of_nonneg_left
      (hc u v (mem_neighbors G u v |>.1 hv)) (hw v)

lemma crossMass_all_right (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    crossMass G w A univ = ∑ u ∈ A, w u * neighborMass G w u := by
  classical
  rw [crossMass_factor]
  simp [neighborMass]

lemma crossMass_all_left (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    crossMass G w univ A = ∑ u ∈ A, w u * neighborMass G w u := by
  rw [crossMass_symm, crossMass_all_right]

end CliqueFreeIndependence.WeightedGraph

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
end EdgeState

omit [Fintype V] in
lemma mass_union_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A B : Finset V) :
    mass w (A ∪ B) ≤ mass w A + mass w B := by
  have h := sum_union_inter (s₁ := A) (s₂ := B) (f := w)
  have hn := mass_nonneg hw (A ∩ B)
  change 0 ≤ ∑ u ∈ A ∩ B, w u at hn
  change (∑ u ∈ A ∪ B, w u) ≤ (∑ u ∈ A, w u) + ∑ u ∈ B, w u
  linarith

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

lemma enlarge_mass (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {L t : ℝ} (hL : ∀ u, neighborMass G w u ≤ L) (ht : 0 < t) (A : Finset V) :
    mass w (enlarge G w t A) ≤ (1 + L / t) * mass w A := by
  let B := univ.filter (fun y ↦ t ≤ mass w (A ∩ neighbors G y))
  have hm : t * mass w B ≤ L * mass w A := by
    calc
      _ = ∑ y ∈ B, w y * t := by rw [← sum_mul]; exact mul_comm _ _
      _ ≤ ∑ y ∈ B, w y * mass w (A ∩ neighbors G y) := by
        exact sum_le_sum fun y hy ↦ mul_le_mul_of_nonneg_left (mem_filter.1 hy).2 (hw y)
      _ ≤ ∑ y, w y * mass w (A ∩ neighbors G y) := by
        exact sum_le_univ_sum_of_nonneg (fun y ↦ mul_nonneg (hw y) (mass_nonneg hw _))
      _ = crossMass G w univ A := (crossMass_factor G w univ A).symm
      _ = ∑ y ∈ A, w y * neighborMass G w y := crossMass_all_left G w A
      _ ≤ ∑ y ∈ A, w y * L := sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left (hL y) (hw y)
      _ = L * mass w A := by rw [← sum_mul]; exact mul_comm _ _
  have hB : mass w B ≤ L / t * mass w A := by
    calc
      _ ≤ L * mass w A / t := (le_div_iff₀ ht).2 (by nlinarith)
      _ = _ := by ring
  have hu := mass_union_le hw A B
  change mass w (A ∪ B) ≤ _
  nlinarith

lemma reach_mass (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {L t : ℝ} (hL0 : 0 ≤ L) (hL : ∀ u, neighborMass G w u ≤ L) (ht : 0 < t)
    (v : V) (n : ℕ) : mass w (reach G w t v n) ≤ (1 + L / t) ^ n * neighborMass G w v := by
  have hfac : 0 ≤ 1 + L / t := by positivity
  induction n with
  | zero => simp [reach, neighborMass]
  | succ n ih =>
    exact (enlarge_mass G hw hL ht _).trans (by
      have h := mul_le_mul_of_nonneg_left ih hfac
      simpa only [pow_succ', mul_assoc] using h)

lemma reach_mass_exp (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {x : ℝ} (hx : 32 ≤ x) (hL : ∀ v, neighborMass G w v ≤ Real.exp x)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * x) (v : V) :
    mass w (reach G w (Numerical.threshold x) v n) ≤ Real.exp (20 * x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have ht := Numerical.threshold_pos hx0
  have hfac : 0 ≤ 1 + Real.exp x / Numerical.threshold x := by positivity
  have hfacn := pow_le_pow_left₀ hfac (Numerical.growth_factor_le hx) n
  calc
    _ ≤ (1 + Real.exp x / Numerical.threshold x) ^ n * neighborMass G w v :=
      reach_mass G hw (Real.exp_pos x).le hL ht v n
    _ ≤ Real.exp (4 * x) ^ n * Real.exp x :=
      mul_le_mul hfacn (hL v) (neighborMass_nonneg G hw v) (by positivity)
    _ = Real.exp ((n : ℝ) * (4 * x) + x) := by rw [Real.exp_add, Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)

lemma growth_le_of_lower {x Y s : ℝ} (hx : 1 ≤ x) (hs : 1 / x ≤ s) :
    growth Y s ≤ s * (Y + Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < s := (one_div_pos.2 hx0).trans_le hs
  have hrec : 1 / s ≤ x := by
    apply (div_le_iff₀ hs0).2
    have h := (div_le_iff₀ hx0).1 hs
    nlinarith
  have hl := Real.log_le_log (one_div_pos.2 hs0) hrec
  have hm : max 0 (Real.log (1 / s)) ≤ Real.log x := max_le (Real.log_nonneg hx) hl
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hm) hs0.le

lemma badSet_subset (G : SimpleGraph V) (w : V → ℝ) (S : V → Finset V)
    (b : ℝ) (v : V) : badSet G w S b v ⊆ neighbors G v := filter_subset _ _

lemma badSet_mass_bound (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 ≤ w u)
    {C Y : ℝ} (hCross : CrossBound G w C) (hY : 1 ≤ Y)
    (S : V → Finset V) (b : ℝ) (v : V)
    (hv : neighborMass G w v ≤ Real.exp Y) (hS : mass w (S v) ≤ Real.exp Y) :
    b * mass w (badSet G w S b v) ≤ C * growth Y (neighborMass G w v) := by
  calc
    _ = ∑ u ∈ badSet G w S b v, w u * b := by rw [← sum_mul]; exact mul_comm _ _
    _ ≤ ∑ u ∈ badSet G w S b v, w u * mass w (S v ∩ neighbors G u) := by
      exact sum_le_sum fun u hu ↦ mul_le_mul_of_nonneg_left ((mem_filter.1 hu).2.le) (hw u)
    _ ≤ ∑ u ∈ neighbors G v, w u * mass w (S v ∩ neighbors G u) := by
      exact sum_le_sum_of_subset_of_nonneg (badSet_subset G w S b v)
        (fun u _ _ ↦ mul_nonneg (hw u) (mass_nonneg hw _))
    _ = crossMass G w (neighbors G v) (S v) := (crossMass_factor _ _ _ _).symm
    _ ≤ _ := hCross Y hY _ _ hv hS

lemma conditional_bad_bound (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 ≤ w u)
    {C x k : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x) (hk : 0 ≤ k)
    (hCross : CrossBound G w C) (v : V) (B : Finset V) (hB : B ⊆ neighbors G v)
    (hs : 1 / x ≤ neighborMass G w v) (hL : neighborMass G w v ≤ Real.exp x)
    (hh : neighborMass G w v / x ≤ triangleAt G w v)
    (hb : mass w B ≤ k * neighborMass G w v) :
    crossMass G w B (neighbors G v) ≤
      (2 * C * x ^ 2 * (k + x * Real.exp (-x))) * triangleAt G w v := by
  have hx0 : 0 < x := by linarith
  have hxsv : 1 ≤ x * neighborMass G w v := by
    have := (div_le_iff₀ hx0).1 hs
    nlinarith
  have hhh : neighborMass G w v ≤ x * triangleAt G w v := by
    have := (div_le_iff₀ hx0).1 hh
    nlinarith
  have he : Real.exp (-x) ≤ x * Real.exp (-x) * neighborMass G w v := by
    nlinarith [mul_le_mul_of_nonneg_left hxsv (Real.exp_pos (-x)).le]
  have hf : 0 ≤ 2 * C * x := by positivity
  have hf' : 0 ≤ 2 * C * x * (k + x * Real.exp (-x)) := by positivity
  calc
    _ ≤ C * growth x (mass w B) := hCross x hx _ _ ((mass_mono hw hB).trans hL) hL
    _ ≤ C * (2 * x * (mass w B + Real.exp (-x))) :=
      mul_le_mul_of_nonneg_left (growth_le_twice hx (mass_nonneg hw B)) hC
    _ = (2 * C * x) * (mass w B + Real.exp (-x)) := by ring
    _ ≤ (2 * C * x) * (k * neighborMass G w v +
        x * Real.exp (-x) * neighborMass G w v) :=
      mul_le_mul_of_nonneg_left (add_le_add hb he) hf
    _ = (2 * C * x * (k + x * Real.exp (-x))) * neighborMass G w v := by ring
    _ ≤ (2 * C * x * (k + x * Real.exp (-x))) * (x * triangleAt G w v) :=
      mul_le_mul_of_nonneg_left hhh hf'
    _ = _ := by ring

lemma reach_bad_mass (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 ≤ w u)
    {C x : ℝ} (hC : 0 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * x) {v : V} (hv : (neighbors G v).Nonempty) :
    mass w (badSet G w (fun u ↦ reach G w (Numerical.threshold x) u n) (x ^ 8) v) ≤
      (21 * C / x ^ 6) * neighborMass G w v := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hY : 1 ≤ 20 * x ^ 2 := by nlinarith
  have hxY : x ≤ 20 * x ^ 2 := by nlinarith
  have hs := neighborMass_ge_of_commonMass G hw hc hv
  have hS := reach_mass_exp G hw hx hL hn v
  have hm := badSet_mass_bound G hw hCross hY
    (fun u ↦ reach G w (Numerical.threshold x) u n) (x ^ 8) v
    ((hL v).trans (Real.exp_le_exp.2 hxY)) hS
  have hg := growth_le_of_lower (Y := 20 * x ^ 2) hx1 hs
  have hlog : Real.log x ≤ x ^ 2 := by
    have := Real.log_le_self hx0.le
    nlinarith
  have hgs : growth (20 * x ^ 2) (neighborMass G w v) ≤
      neighborMass G w v * (21 * x ^ 2) := by
    apply hg.trans
    apply mul_le_mul_of_nonneg_left _ (neighborMass_nonneg G hw v)
    linarith
  have hm' := hm.trans (mul_le_mul_of_nonneg_left hgs hC)
  calc
    _ ≤ C * (neighborMass G w v * (21 * x ^ 2)) / x ^ 8 := by
      apply (le_div_iff₀ (pow_pos hx0 8)).2
      nlinarith [hm']
    _ = _ := by field_simp [hx0.ne']

lemma reach_bad_cross (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 ≤ w u)
    {C x : ℝ} (hC : 0 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * x) (v : V) :
    crossMass G w (badSet G w (fun u ↦ reach G w (Numerical.threshold x) u n) (x ^ 8) v)
      (neighbors G v) ≤ (exceptionalConstant C / x ^ 4) * triangleAt G w v := by
  have hx0 : 0 < x := by linarith
  by_cases hv : (neighbors G v).Nonempty
  · have hbad := reach_bad_mass G hw hC hCross hx hL hc hn hv
    have hcond := conditional_bad_bound G hw hC (show 1 ≤ x by linarith)
      (show 0 ≤ 21 * C / x ^ 6 by positivity) hCross v _
      (badSet_subset G w _ _ v) (neighborMass_ge_of_commonMass G hw hc hv) (hL v)
      (by simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using triangleAt_ge_of_commonMass G hw hc v)
      hbad
    have hnum : 2 * C * x ^ 2 * (21 * C / x ^ 6 + x * Real.exp (-x)) ≤
        exceptionalConstant C / x ^ 4 := by
      calc
        _ ≤ 2 * C * x ^ 2 * (21 * C / x ^ 6 + x * (1 / x ^ 7)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Numerical.exp_neg_le_inv_pow_seven hx) hx0.le)
        _ = _ := by unfold exceptionalConstant; field_simp [hx0.ne']; ring
    exact hcond.trans (mul_le_mul_of_nonneg_right hnum (triangleAt_nonneg G hw v))
  · have he := not_nonempty_iff_eq_empty.1 hv
    simp [badSet, he, crossMass, triangleAt]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance 10000] edgeStateDecEq


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.reach_bad_cross.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.reach_bad_cross.{u}
