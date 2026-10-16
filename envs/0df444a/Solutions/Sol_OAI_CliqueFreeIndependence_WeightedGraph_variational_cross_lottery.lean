-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.variational_cross_lottery
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:57:01.249972+00:00
-- url     : https://prove2.me/submissions/a6d7a2ec-fca4-425b-baaf-82dc410abf18

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/VariationalCross.lean:L100-L171
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.variational_cross_lottery. The node keeps its source
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
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_edgeMass_restrict
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_edgeMass_smul
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_divergence
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_stationary

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
lemma crossMass_le_product (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (A B : Finset V) : crossMass G w A B ≤ mass w A * mass w B := by
  classical
  unfold crossMass mass
  rw [sum_mul_sum]
  exact sum_le_sum fun u _ ↦ sum_le_sum fun v _ ↦ by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hw u) (hw v)

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.Optimizer ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
universe u
variable {V : Type u} [Fintype V]

lemma edgeForm_self (G : SimpleGraph V) (a : V → ℝ) : edgeForm G a a = 2 * edgeMass G a := by
  simp only [edgeForm,edgeMass,crossMass]
  ring

lemma edgeForm_symm (G : SimpleGraph V) (a b : V → ℝ) : edgeForm G a b = edgeForm G b a := by
  unfold edgeForm
  rw [sum_comm]
  simp_rw [G.adj_comm,mul_comm]

lemma edgeForm_add_left (G : SimpleGraph V) (a b c : V → ℝ) :
    edgeForm G (a+b) c = edgeForm G a c + edgeForm G b c := by
  unfold edgeForm
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro u _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  split_ifs <;> simp [Pi.add_apply,add_mul]

lemma edgeForm_add_right (G : SimpleGraph V) (a b c : V → ℝ) :
    edgeForm G a (b+c) = edgeForm G a b + edgeForm G a c := by
  rw [edgeForm_symm,edgeForm_add_left,edgeForm_symm _ b,edgeForm_symm _ c]

lemma edgeForm_neighbor (G : SimpleGraph V) (a b : V → ℝ) :
    edgeForm G a b = ∑ u, a u * neighborMass G b u := by
  simp only [edgeForm,neighborMass,mass,neighbors,sum_filter,mul_sum,mul_ite,mul_zero]

lemma edgeMass_add (G : SimpleGraph V) (a b : V → ℝ) :
    edgeMass G (a+b) = edgeMass G a + edgeMass G b + edgeForm G a b := by
  have h := edgeForm_self G (a+b)
  rw [edgeForm_add_left,edgeForm_add_right,edgeForm_add_right,edgeForm_self,edgeForm_self,
    edgeForm_symm G b a] at h
  linarith

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.Lottery ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence
universe u
namespace Lottery
variable {α β : Type u}

lemma expect_add (L : Law α) (f g : α → ℝ) :
    expect L (fun a ↦ f a + g a) = expect L f + expect L g := by
  induction L with
  | nil => simp
  | cons z L ih =>
    rcases z with ⟨p,a⟩
    simp only [expect_cons,ih]
    ring

lemma expect_mul (L : Law α) (a : ℝ) (f : α → ℝ) :
    expect L (fun z ↦ a*f z) = a * expect L f := by
  induction L with
  | nil => simp
  | cons z L ih =>
    rcases z with ⟨p,a⟩
    simp only [expect_cons,ih]
    ring

lemma expect_const (L : Law α) (a : ℝ) : expect L (fun _ ↦ a) = a * total L := by
  simpa only [mul_one,total] using expect_mul L a (fun _ ↦ 1)

lemma expect_mono {L : Law α} (hL : Positive L) {f g : α → ℝ}
    (h : ∀ z ∈ L, f z.2 ≤ g z.2) : expect L f ≤ expect L g := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    exact add_le_add (mul_le_mul_of_nonneg_left (h z (by simp)) (hL z (by simp)))
      (ih (fun t ht ↦ hL t (by simp [ht])) (fun t ht ↦ h t (by simp [ht])))

lemma expect_sum {I : Type*} (L : Law α) (s : Finset I) (f : I → α → ℝ) :
    expect L (fun a ↦ ∑ i ∈ s, f i a) = ∑ i ∈ s, expect L (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expect_const]
  | @insert i s hi ih => simp only [sum_insert hi,expect_add,ih]

end Lottery

end CliqueFreeIndependence

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.VariationalCross ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
open Lottery
universe u
variable {V : Type u} [Fintype V]

lemma edgeForm_smul_left (G : SimpleGraph V) (a b : V → ℝ) (t : ℝ) :
    edgeForm G (fun v ↦ t*a v) b = t*edgeForm G a b := by
  unfold edgeForm
  simp only [mul_sum,mul_ite,mul_zero]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  split_ifs <;> ring

lemma edgeForm_smul_right (G : SimpleGraph V) (a b : V → ℝ) (t : ℝ) :
    edgeForm G a (fun v ↦ t*b v) = t*edgeForm G a b := by
  rw [edgeForm_symm,edgeForm_smul_left,edgeForm_symm G b a]

lemma edgeMass_lin_sub (G : SimpleGraph V) (a b : V → ℝ) (k : ℝ) :
    edgeMass G (fun v ↦ k*a v-b v) =
      k^2*edgeMass G a + edgeMass G b - k*edgeForm G a b := by
  have he : (fun v ↦ k*a v-b v) = (fun v ↦ k*a v)+(fun v ↦ (-1)*b v) := by
    ext v; simp; ring
  rw [he,edgeMass_add,edgeMass_smul,edgeMass_smul,edgeForm_smul_left,edgeForm_smul_right]
  ring

lemma edgeForm_restrict (G : SimpleGraph V) (w : V → ℝ) (S D : Finset V) :
    edgeForm G (restrict S w) (restrict D w) = crossMass G w S D := by
  classical
  unfold edgeForm crossMass restrict
  calc
    _ = ∑ u, if u ∈ S then ∑ v, if v ∈ D then (if G.Adj u v then w u*w v else 0) else 0 else 0 := by
      apply sum_congr rfl
      intro u _
      by_cases hu : u ∈ S
      · simp only [hu,ite_true]
        apply sum_congr rfl
        intro v _
        by_cases hv : v ∈ D <;> simp [hv]
      · simp [hu]
    _ = _ := by
      rw [← sum_filter]
      simp only [filter_mem_eq_inter,univ_inter]
      apply sum_congr rfl
      intro u hu
      rw [← sum_filter]
      simp

lemma expected_weight (w : V → ℝ) (L : Law (V → ℝ)) (S : Finset V)
    (hmean : ∀ v, expect L (fun m ↦ m v) = if v ∈ S then 1 else 0) :
    expect L (fun m ↦ ∑ v, w v*m v) = mass w S := by
  classical
  rw [expect_sum]
  simp_rw [Lottery.expect_mul,hmean,mul_ite,mul_one,mul_zero]
  rw [← sum_filter]
  simp [mass]

lemma expected_edgeForm (G : SimpleGraph V) (w : V → ℝ) (L : Law (V → ℝ)) (S D : Finset V)
    (hmean : ∀ v, expect L (fun m ↦ m v) = if v ∈ S then 1 else 0) :
    expect L (fun m ↦ edgeForm G (fun v ↦ w v*m v) (restrict D w)) = crossMass G w S D := by
  classical
  rw [← edgeForm_restrict]
  simp only [edgeForm_neighbor]
  rw [expect_sum]
  apply sum_congr rfl
  intro u _
  have hf : (fun m : V → ℝ ↦ w u*m u*neighborMass G (restrict D w) u) =
      (fun m ↦ (w u*neighborMass G (restrict D w) u)*m u) := by ext m; ring
  rw [hf,Lottery.expect_mul,hmean]
  by_cases hu : u ∈ S <;> simp [restrict,hu]

lemma vertex_divergence_upper {w y L : ℝ} (hw : 0 < w) (hy : 0 ≤ y) (hL : y ≤ L) :
    (w*(1+y))*Real.log ((w*(1+y))/w) - w*(1+y) + w ≤ w*y*Real.log (1+L) := by
  have hy1 : 0 < 1+y := by linarith
  have hL1 : 0 < 1+L := hy1.trans_le (by linarith)
  have hlog := Real.log_le_sub_one_of_pos hy1
  have hmono := Real.log_le_log hy1 (by linarith : 1+y ≤ 1+L)
  have hlo : w*y*Real.log (1+y) ≤ w*y*Real.log (1+L) :=
    mul_le_mul_of_nonneg_left hmono (mul_nonneg hw.le hy)
  have hcancel : w*(1+y)/w = 1+y := by field_simp
  rw [hcancel]
  nlinarith [mul_le_mul_of_nonneg_left hlog hw.le]

lemma variational_cross_lottery (G : SimpleGraph V) {w : V → ℝ} (hw : IsOptimizer G w)
    (S D : Finset V) (hSD : Disjoint S D) (L : Law (V → ℝ)) (hp : IsProb L)
    {b k ε : ℝ} (hk : 0 ≤ k) (hb : BoundedOn L S b)
    (hm : ∀ v, expect L (fun m ↦ m v) = if v ∈ S then 1 else 0)
    (he : expectedEdges G w L ≤ ε*(mass w S)^2) :
    k*crossMass G w S D ≤ k^2*ε*(mass w S)^2 + (mass w D)^2/2 + mass w D +
      k*Real.log (1+k*b)*mass w S := by
  classical
  have hwpos := fun v ↦ (optimizer_stationary hw v).1
  have hw0 := fun v ↦ (hwpos v).le
  let cost (m : V → ℝ) : ℝ :=
    k*Real.log (1+k*b)*(∑ v, w v*m v) + mass w D +
      (k^2*edgeMass G (fun v ↦ w v*m v) + edgeMass G (restrict D w) -
        k*edgeForm G (fun v ↦ w v*m v) (restrict D w))
  have hcost (z : ℝ × (V → ℝ)) (hz : z ∈ L) : 0 ≤ cost z.2 := by
    let m := z.2
    have hm0 := fun v ↦ (hb z hz).1 v |>.1
    have hmb := fun v ↦ (hb z hz).1 v |>.2
    have hmD (v : V) (hv : v ∈ D) : m v = 0 :=
      (hb z hz).2 v (disjoint_left.1 hSD · hv)
    let q : V → ℝ := fun v ↦ if v ∈ D then 0 else w v*(1+k*m v)
    have hq (v : V) : 0 ≤ q v := by
      dsimp [q]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hw0 v) (by nlinarith [mul_nonneg hk (hm0 v)])
    obtain ⟨hdiv,heq⟩ := optimizer_divergence hw q hq
    rw [heq] at hdiv
    have hve (v : V) : q v*Real.log (q v/w v)-q v+w v ≤
        k*Real.log (1+k*b)*(w v*m v) + if v ∈ D then w v else 0 := by
      by_cases hv : v ∈ D
      · simp [q,hv,hmD v hv]
      · have hh := vertex_divergence_upper (hwpos v) (mul_nonneg hk (hm0 v))
          (mul_le_mul_of_nonneg_left (hmb v) hk)
        dsimp [q]
        rw [ite_eq_right hv,ite_eq_right hv]
        nlinarith only [hh]
    have hD : (∑ v, if v ∈ D then w v else 0) = mass w D := by
      rw [← sum_filter]; simp [mass]
    have hvs : (∑ v, (q v*Real.log (q v/w v)-q v+w v)) ≤
        k*Real.log (1+k*b)*(∑ v, w v*m v) + mass w D := by
      calc
        _ ≤ ∑ v, (k*Real.log (1+k*b)*(w v*m v) + if v ∈ D then w v else 0) :=
          sum_le_sum fun v _ ↦ hve v
        _ = _ := by rw [sum_add_distrib,← mul_sum,hD]
    have hqsub : q-w = fun v ↦ k*(w v*m v)-restrict D w v := by
      ext v
      by_cases hv : v ∈ D <;> simp [q,restrict,hv,hmD v,Pi.sub_apply]
      ring
    rw [hqsub,edgeMass_lin_sub] at hdiv
    dsimp [cost,m]
    linarith only [hdiv,hvs]
  have havg : 0 ≤ expect L cost := by
    have hh := expect_mono hp.1 (f := fun _ ↦ 0) (g := cost) (fun z hz ↦ hcost z hz)
    simpa [Lottery.expect_const] using hh
  have hec : expect L cost =
      k*Real.log (1+k*b)*mass w S + mass w D +
        (k^2*expectedEdges G w L + edgeMass G (restrict D w) - k*crossMass G w S D) := by
    have hsub (a b : (V → ℝ) → ℝ) : expect L (fun m ↦ a m-b m) = expect L a-expect L b := by
      have hf : (fun m ↦ a m-b m) = (fun m ↦ a m+(-1)*b m) := by ext m; ring
      rw [hf,expect_add,Lottery.expect_mul]; ring
    dsimp [cost]
    rw [expect_add,expect_add,hsub,expect_add,Lottery.expect_mul,expected_weight w L S hm,
      Lottery.expect_const,hp.2,mul_one,Lottery.expect_mul,Lottery.expect_const,hp.2,mul_one,Lottery.expect_mul,
      expected_edgeForm G w L S D hm]
    rfl
  rw [hec] at havg
  have hDedge : edgeMass G (restrict D w) ≤ (mass w D)^2/2 := by
    rw [edgeMass_restrict]
    exact div_le_div_of_nonneg_right (by simpa [sq] using crossMass_le_product G hw0 D D) (by norm_num)
  have hmult := mul_le_mul_of_nonneg_left he (sq_nonneg k)
  nlinarith only [havg,hDedge,hmult]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Lottery


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.variational_cross_lottery.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.variational_cross_lottery.{u}
