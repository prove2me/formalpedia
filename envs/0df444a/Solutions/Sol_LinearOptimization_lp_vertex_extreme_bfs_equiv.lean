-- Prove2me | solution 1 for LinearOptimization.lp_vertex_extreme_bfs_equiv
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-05T05:52:01.363379+00:00
-- url     : https://prove2.me/submissions/df09e489-5f6a-42fb-9212-0b00df6b503e

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Segment
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.List.TFAE
import Definitions.Def_Vertex
import Definitions.Def_BasicSolution
import Theorems.Thm_LinearOptimization_lp_active_constraint_equiv

open Matrix LinearOptimization

/-- The subspace of vectors orthogonal to a fixed `d`. -/
private def orthTo {n : ℕ} (d : Fin n → ℝ) : Submodule ℝ (Fin n → ℝ) where
  carrier := {v | v ⬝ᵥ d = 0}
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq, add_dotProduct] at *
    rw [hu, hv, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c v hv
    simp only [Set.mem_setOf_eq, smul_dotProduct] at *
    rw [hv, smul_zero]

/-- `n` linearly independent active constraints pin down at most one point
(uniqueness half of B&T Theorem 2.2). -/
private lemma unique_of_indep {ι : Type} {n : ℕ} (C : ι → LinearConstraint n) (s : Finset ι)
    (hcard : s.card = n) (hli : LinearIndependent ℝ (fun i : s => (C i.1).a))
    {x y : Fin n → ℝ} (hx : ∀ i ∈ s, (C i).a ⬝ᵥ x = (C i).b)
    (hy : ∀ i ∈ s, (C i).a ⬝ᵥ y = (C i).b) : x = y := by
  have hfr : Module.finrank ℝ (Fin n → ℝ) = n := by
    rw [Module.finrank_pi ℝ, Fintype.card_fin]
  have hspan : Submodule.span ℝ (Set.range (fun i : s => (C i.1).a)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_coe, hcard, hfr])
  have hsub : Set.range (fun i : s => (C i.1).a) ⊆ (orthTo (x - y) : Set (Fin n → ℝ)) := by
    rintro w ⟨i, rfl⟩
    show (C i.1).a ⬝ᵥ (x - y) = 0
    rw [dotProduct_sub, hx i.1 i.2, hy i.1 i.2, sub_self]
  have htop : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ orthTo (x - y) := by
    rw [← hspan]; exact Submodule.span_le.mpr hsub
  have : (x - y) ⬝ᵥ (x - y) = 0 := htop (Submodule.mem_top)
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp this)

theorem solution {ι : Type} [Fintype ι] {n : ℕ}
    (C : ι → LinearConstraint n) (x' : Fin n → ℝ)
    (hne : (constraintSet C).Nonempty) (hx : x' ∈ constraintSet C) :
    List.TFAE
      [ IsVertex (constraintSet C) x',
        x' ∈ Set.extremePoints ℝ (constraintSet C),
        IsBasicFeasibleSolution C x' ] := by
  classical
  -- A feasible point activates every equality constraint.
  have heq_active : ∀ i, (C i).rel = .eq → (C i).IsActiveAt x' := by
    intro i hi
    have h := hx i
    show (C i).a ⬝ᵥ x' = (C i).b
    simp only [LinearConstraint.IsSatisfiedAt, hi] at h
    exact h
  tfae_have 1 → 2 := by
    rintro ⟨hmem, c, hc⟩
    refine ⟨hmem, ?_⟩
    intro y hy z hz hseg
    obtain ⟨a, b, ha, hb, hab, hxeq⟩ := hseg
    have key : ∀ w ∈ constraintSet C, c ⬝ᵥ x' ≤ c ⬝ᵥ w := by
      intro w hw
      rcases eq_or_ne w x' with rfl | hne'
      · exact le_refl _
      · exact (hc w hw hne').le
    have hy' : c ⬝ᵥ x' ≤ c ⬝ᵥ y := key y hy
    have hz' : c ⬝ᵥ x' ≤ c ⬝ᵥ z := key z hz
    have hsum : c ⬝ᵥ x' = a * (c ⬝ᵥ y) + b * (c ⬝ᵥ z) := by
      rw [← hxeq, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    by_contra hne'
    have hlt := hc y hy hne'
    have h1 : a * (c ⬝ᵥ x') < a * (c ⬝ᵥ y) := mul_lt_mul_of_pos_left hlt ha
    have h2 : b * (c ⬝ᵥ x') ≤ b * (c ⬝ᵥ z) := mul_le_mul_of_nonneg_left hz' hb.le
    have h3 : a * (c ⬝ᵥ x') + b * (c ⬝ᵥ x') = c ⬝ᵥ x' := by
      rw [← add_mul, hab, one_mul]
    linarith
  tfae_have 3 → 1 := by
    rintro ⟨⟨heq, s, hcard, hact, hli⟩, hmem⟩
    refine ⟨hmem, ?_⟩
    set σ : ι → ℝ := fun i => if (C i).rel = ConstraintRel.le then -1 else 1 with hσ
    have hσne : ∀ i, σ i ≠ 0 := by
      intro i; rw [hσ]; dsimp only; split <;> norm_num
    refine ⟨∑ i ∈ s, σ i • (C i).a, ?_⟩
    intro y hy hyne
    -- every feasible point beats the active right-hand sides, coordinate by coordinate
    have hle : ∀ i ∈ s, σ i * (C i).b ≤ σ i * ((C i).a ⬝ᵥ y) := by
      intro i _
      have hsat := hy i
      rcases hr : (C i).rel with _ | _ | _
      · have hs1 : σ i = 1 := by simp [hσ, hr]
        simp only [LinearConstraint.IsSatisfiedAt, hr] at hsat
        rw [hs1]; linarith
      · have hs1 : σ i = -1 := by simp [hσ, hr]
        simp only [LinearConstraint.IsSatisfiedAt, hr] at hsat
        rw [hs1]; linarith
      · have hs1 : σ i = 1 := by simp [hσ, hr]
        simp only [LinearConstraint.IsSatisfiedAt, hr] at hsat
        rw [hs1]; linarith
    have hx_eq : (∑ i ∈ s, σ i • (C i).a) ⬝ᵥ x' = ∑ i ∈ s, σ i * (C i).b := by
      rw [sum_dotProduct]
      exact Finset.sum_congr rfl fun i hi => by
        rw [smul_dotProduct, smul_eq_mul, hact i hi]
    have hy_eq : (∑ i ∈ s, σ i • (C i).a) ⬝ᵥ y = ∑ i ∈ s, σ i * ((C i).a ⬝ᵥ y) := by
      rw [sum_dotProduct]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_dotProduct, smul_eq_mul]
    rw [hx_eq, hy_eq]
    rcases lt_or_eq_of_le (Finset.sum_le_sum hle) with h | h
    · exact h
    · exfalso
      have hterm : ∀ i ∈ s, (C i).a ⬝ᵥ y = (C i).b := by
        intro i hi
        by_contra hne2
        have hlt : σ i * (C i).b < σ i * ((C i).a ⬝ᵥ y) :=
          lt_of_le_of_ne (hle i hi) (fun hEq => hne2 (by
            have := mul_left_cancel₀ (hσne i) hEq
            exact this.symm))
        have := Finset.sum_lt_sum hle ⟨i, hi, hlt⟩
        linarith
      exact hyne (unique_of_indep C s hcard hli hterm (fun i hi => hact i hi))
  tfae_have 2 → 3 := by
    intro hext
    by_contra hnbfs
    have hnb : ¬ IsBasicSolution C x' := fun h => hnbfs ⟨h, hx⟩
    have hns : ¬ ∃ s : Finset ι, s.card = n ∧ (∀ i ∈ s, (C i).IsActiveAt x') ∧
        LinearIndependent ℝ (fun i : s => (C i.1).a) := fun h => hnb ⟨heq_active, h⟩
    -- Theorem 2.2: failing (a) means the uniqueness statement (c) also fails.
    have hn3 : ¬ (∀ y : Fin n → ℝ,
        (∀ i, (C i).IsActiveAt x' → (C i).a ⬝ᵥ y = (C i).b) → y = x') := by
      intro h3
      exact hns (((lp_active_constraint_equiv C x').out 2 0).mp h3)
    push_neg at hn3
    obtain ⟨y0, hy0, hy0ne⟩ := hn3
    set d : Fin n → ℝ := y0 - x' with hdd
    have hd0 : d ≠ 0 := sub_ne_zero.mpr hy0ne
    have hdorth : ∀ i, (C i).IsActiveAt x' → (C i).a ⬝ᵥ d = 0 := by
      intro i hi
      have h1 : (C i).a ⬝ᵥ x' = (C i).b := hi
      rw [hdd, dotProduct_sub, hy0 i hi, h1, sub_self]
    -- Moving off `x'` along `d` stays feasible for small steps.
    have hev : ∀ᶠ ε : ℝ in nhds (0:ℝ), ∀ i, (C i).IsSatisfiedAt (x' + ε • d) := by
      rw [Filter.eventually_all]
      intro i
      by_cases hact : (C i).IsActiveAt x'
      · filter_upwards with ε
        have hval : (C i).a ⬝ᵥ (x' + ε • d) = (C i).b := by
          rw [dotProduct_add, dotProduct_smul, hdorth i hact, smul_zero, add_zero]
          exact hact
        rcases hr : (C i).rel with _ | _ | _ <;>
          simp only [LinearConstraint.IsSatisfiedAt, hr, hval] <;> norm_num
      · have hcont : Filter.Tendsto (fun ε : ℝ => (C i).a ⬝ᵥ (x' + ε • d)) (nhds 0)
            (nhds ((C i).a ⬝ᵥ x')) := by
          have : Continuous fun ε : ℝ => (C i).a ⬝ᵥ (x' + ε • d) := by
            simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
            exact continuous_const.add (continuous_id.mul continuous_const)
          have h0 := this.tendsto 0
          simpa using h0
        have hsat := hx i
        have hrel : (C i).rel ≠ ConstraintRel.eq := fun h => hact (heq_active i h)
        rcases hr : (C i).rel with _ | _ | _
        · -- ≥ : strict slack at x'
          simp only [LinearConstraint.IsSatisfiedAt, hr] at hsat
          have hlt : (C i).b < (C i).a ⬝ᵥ x' :=
            lt_of_le_of_ne hsat (fun h => hact h.symm)
          filter_upwards [hcont.eventually_const_le hlt] with ε hε
          simp only [LinearConstraint.IsSatisfiedAt, hr]
          exact hε
        · -- ≤ : strict slack at x'
          simp only [LinearConstraint.IsSatisfiedAt, hr] at hsat
          have hlt : (C i).a ⬝ᵥ x' < (C i).b :=
            lt_of_le_of_ne hsat (fun h => hact h)
          filter_upwards [hcont.eventually_le_const hlt] with ε hε
          simp only [LinearConstraint.IsSatisfiedAt, hr]
          exact hε
        · exact absurd hr hrel
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨r, hr, hball⟩ := hev
    have hεpos : (0:ℝ) < r / 2 := by linarith
    have hdist : ∀ t : ℝ, |t| = r / 2 → dist t (0:ℝ) < r := by
      intro t ht
      rw [Real.dist_eq, sub_zero, ht]; linarith
    have hplus : x' + (r/2) • d ∈ constraintSet C :=
      hball (hdist (r/2) (by rw [abs_of_pos hεpos]))
    have hminus : x' + (-(r/2)) • d ∈ constraintSet C :=
      hball (hdist (-(r/2)) (by rw [abs_neg, abs_of_pos hεpos]))
    -- `x'` is the midpoint of these two distinct feasible points
    have hmid : x' ∈ openSegment ℝ (x' + (r/2) • d) (x' + (-(r/2)) • d) := by
      refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      ext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul]
      ring
    have hcontra := hext.2 hplus hminus hmid
    have : (r/2) • d = 0 := by
      have := congrArg (fun z => z - x') hcontra
      simpa using this
    have : d = 0 := by
      rcases smul_eq_zero.mp this with h | h
      · exact absurd h (by positivity)
      · exact h
    exact hd0 this
  tfae_finish
