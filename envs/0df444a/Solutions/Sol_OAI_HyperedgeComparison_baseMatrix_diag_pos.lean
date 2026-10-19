-- Prove2me | solution 1 for OAI.HyperedgeComparison.baseMatrix_diag_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:34:08.427953+00:00
-- url     : https://prove2.me/submissions/7d529296-3b42-4eed-9bd7-1437fed0f7ff

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison

open OAI OAI.HyperedgeComparison
universe uE uI uV
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
variable {V : Type uV} {E : Type uE}
variable [Fintype E]
theorem hc_adj_symm {V E : Type*} {H : OAI.HyperedgeComparison.Hypergraph V E} {ω : E → Bool}
    {D : Set V} {x y : V} (h : OAI.HyperedgeComparison.Adj H ω D x y) :
    OAI.HyperedgeComparison.Adj H ω D y x := by
  obtain ⟨e, h1, h2, h3, h4⟩ := h
  exact ⟨e, h1, h2, h4, h3⟩

theorem hc_conn_symm {V E : Type*} {H : OAI.HyperedgeComparison.Hypergraph V E} {ω : E → Bool}
    {D : Set V} {x y : V} (h : OAI.HyperedgeComparison.Connected H ω D x y) :
    OAI.HyperedgeComparison.Connected H ω D y x := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact Relation.ReflTransGen.head (hc_adj_symm hab) ih

theorem hc_conn_trans {V E : Type*} {H : OAI.HyperedgeComparison.Hypergraph V E} {ω : E → Bool}
    {D : Set V} {x y z : V} (h : OAI.HyperedgeComparison.Connected H ω D x y)
    (h' : OAI.HyperedgeComparison.Connected H ω D y z) :
    OAI.HyperedgeComparison.Connected H ω D x z :=
  Relation.ReflTransGen.trans h h'

theorem hc_conn_false {V E : Type*} {H : OAI.HyperedgeComparison.Hypergraph V E}
    {D : Set V} {x y : V} (h : OAI.HyperedgeComparison.Connected H (fun _ => false) D x y) :
    y = x := by
  induction h with
  | refl => rfl
  | tail _ hab _ => obtain ⟨e, h1, _⟩ := hab; simp at h1
theorem hc_law_real_singleton {E : Type*} [Fintype E] (p : E → Set.Icc (0 : ℝ) 1) (ω : E → Bool) :
    (law p).real {ω} = ∏ e, (if ω e then (p e : ℝ) else 1 - (p e : ℝ)) := by
  have hs : ({ω} : Set (E → Bool)) = Set.univ.pi (fun e => {ω e}) := by
    ext η; simp [funext_iff]
  rw [hs, measureReal_def, law, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  cases h : ω e
  · rw [← measureReal_def, bernoulliMeasure_real_apply_of_notMem_of_mem _ (measurableSet_singleton _) (by simp) (by simp)]
    simp
  · rw [← measureReal_def, bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton _) (by simp) (by simp)]
    simp

theorem hc_law_false_pos {E : Type*} [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (hp : ∀ e, (p e : ℝ) < 1) : 0 < (law p).real {fun _ => false} := by
  rw [hc_law_real_singleton]
  exact Finset.prod_pos (fun e _ => by simp only [Bool.false_eq_true, if_false]; linarith [hp e])

theorem hc_integral_ge_point {E : Type*} [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (f : (E → Bool) → ℝ) (hf : ∀ ω, 0 ≤ f ω) (ω0 : E → Bool) :
    (law p).real {ω0} * f ω0 ≤ ∫ ω, f ω ∂law p := by
  rw [integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul]
  exact Finset.single_le_sum (f := fun ω => (law p).real {ω} * f ω)
    (fun ω _ => mul_nonneg measureReal_nonneg (hf ω)) (Finset.mem_univ ω0)

theorem solution {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) :
    0 < baseMatrix H p x k k := by
  unfold baseMatrix column
  refine lt_of_lt_of_le ?_ (hc_integral_ge_point p _ (fun ω => by split_ifs <;> norm_num) (fun _ => false))
  rw [if_pos]
  · simpa using hc_law_false_pos p hp
  · refine ⟨Set.disjoint_left.mpr ?_, .refl⟩
    rintro y hy ⟨j, hj, rfl⟩
    have := hx (hc_conn_false hy)
    subst this
    exact lt_irrefl _ hj

