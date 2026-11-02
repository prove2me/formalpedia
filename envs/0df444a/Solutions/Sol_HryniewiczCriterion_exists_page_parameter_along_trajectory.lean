-- Prove2me | solution 1 for HryniewiczCriterion.exists_page_parameter_along_trajectory
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T16:12:26.999742+00:00
-- url     : https://prove2.me/submissions/d58f9abc-4ced-4b78-8903-462ac08216fb

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.MonotoneConvergence
import Theorems.Thm_HryniewiczCriterion_trajectory_not_mem_image_of_start
import Theorems.Thm_HryniewiczCriterion_exists_continuous_lift_of_continuous_mod_one
import Theorems.Thm_HryniewiczCriterion_exists_local_page_branch
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.Order.Floor

open HryniewiczCriterion
open scoped ContDiff
open Filter Topology

/-!
# Glue for `exists_page_parameter_along_trajectory`

The fibration gives a page parameter in `[0, 1)` at each time. Near each time it agrees modulo
`1` with a local branch with non-zero derivative, so it is continuous modulo `1` and has a
continuous lift `Θ`. The lift differs from each local branch by a locally constant integer, so it
has a non-zero derivative everywhere, and by Darboux's theorem it is strictly monotone.
-/


noncomputable section

namespace HryniewiczCriterion

lemma ppa_page_int (page : ℝ → Plane → R4) (hper : ∀ θ u, page (θ + 1) u = page θ u)
    (θ : ℝ) (n : ℤ) : page (θ + n) = page θ := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    funext u
    calc page (θ + ((k + 1 : ℤ) : ℝ)) u = page (θ + (k : ℝ) + 1) u := by
          congr 1; push_cast; ring
      _ = page (θ + (k : ℝ)) u := hper _ u
      _ = page θ u := by simpa using congrFun ih u
  | pred k ih =>
    funext u
    calc page (θ + ((-(k : ℤ) - 1 : ℤ) : ℝ)) u = page (θ + (-(k : ℝ) - 1)) u := by
          congr 1; push_cast; ring
      _ = page (θ + (-(k : ℝ) - 1) + 1) u := (hper _ u).symm
      _ = page (θ + ((-(k : ℤ) : ℤ) : ℝ)) u := by congr 1; push_cast; ring
      _ = page θ u := congrFun ih u

lemma ppa_coe_add_int (a : ℝ) (n : ℤ) :
    (((a + n : ℝ)) : AddCircle (1 : ℝ)) = (a : AddCircle (1 : ℝ)) := by
  rw [QuotientAddGroup.eq]
  exact AddSubgroup.mem_zmultiples_iff.2 ⟨-n, by simp⟩

lemma ppa_int_eq (a b : ℤ) (h : dist (a : ℝ) b < 1) : a = b := by
  rw [Real.dist_eq, abs_lt] at h
  have h1 : ((a - b : ℤ) : ℝ) < 1 := by push_cast; linarith
  have h2 : (-1 : ℝ) < ((a - b : ℤ) : ℝ) := by push_cast; linarith
  have h1' : a - b < 1 := by exact_mod_cast h1
  have h2' : -1 < a - b := by exact_mod_cast h2
  omega

theorem exists_page_parameter_along_trajectory_aux (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H)
    (page : ℝ → Plane → R4)
    (hob : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2) ∧
      (∀ θ u, page (θ + 1) u = page θ u) ∧
      (∀ θ, IsSmoothDiskEmbedding (page θ)) ∧
      (∀ θ, page θ '' closedUnitDisk ⊆ energySurface H) ∧
      (∀ θ t, page θ (circlePoint t) = P.x (P.T * t)) ∧
      (∀ θ, ∀ u ∈ openUnitDisk,
        hamiltonianVectorField H (page θ u) ∉ Set.range (fderiv ℝ (page θ) u)) ∧
      (∀ y ∈ energySurface H, y ∉ P.image →
        ∃! z : ℝ × Plane, z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ openUnitDisk ∧ page z.1 z.2 = y) ∧
      (∀ θ : ℝ, ∀ u ∈ openUnitDisk,
        Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u))))
    (y : ℝ → R4) (hy : IsTrajectory H y) (hy0 : y 0 ∉ P.image) :
    ∃ (Θ : ℝ → ℝ) (u : ℝ → Plane), Continuous Θ ∧ (StrictMono Θ ∨ StrictAnti Θ) ∧
      ∀ t, u t ∈ openUnitDisk ∧ page (Θ t) (u t) = y t := by
  obtain ⟨hsm, hper, -, hDS, -, htr, hfib, hreg⟩ := hob
  have hoff : ∀ t, y t ∉ P.image := trajectory_not_mem_image_of_start H hS.1 P y hy hy0
  have hfib' : ∀ t, ∃! z : ℝ × Plane,
      z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ openUnitDisk ∧ page z.1 z.2 = y t :=
    fun t => hfib (y t) (hy.2 t) (hoff t)
  choose z hz hzu using hfib'
  set θ₀ : ℝ → ℝ := fun t => (z t).1 with hθ₀
  -- local branches
  have hloc : ∀ t₀, ∃ (θ : ℝ → ℝ) (c : ℝ), c ≠ 0 ∧ HasDerivAt θ c t₀ ∧ θ t₀ = θ₀ t₀ ∧
      ∀ᶠ t in 𝓝 t₀, ∃ n : ℤ, θ₀ t = θ t + n := by
    intro t₀
    obtain ⟨θ, u, c, hc, hd, h0, hev⟩ := exists_local_page_branch H hS page hsm hDS htr hreg y hy
      t₀ (z t₀).1 (z t₀).2 (hz t₀).2.1 (hz t₀).2.2
    refine ⟨θ, c, hc, hd, h0, ?_⟩
    filter_upwards [hev] with t ht
    obtain ⟨hut, hpt⟩ := ht
    have hspec : (Int.fract (θ t)) ∈ Set.Ico (0 : ℝ) 1 ∧ u t ∈ openUnitDisk ∧
        page (Int.fract (θ t)) (u t) = y t := by
      refine ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, hut, ?_⟩
      have : Int.fract (θ t) = θ t + ((-⌊θ t⌋ : ℤ) : ℝ) := by
        rw [Int.fract]; push_cast; ring
      rw [this, ppa_page_int page hper]; exact hpt
    have heq := hzu t (Int.fract (θ t), u t) hspec
    refine ⟨-⌊θ t⌋, ?_⟩
    have h1 : Int.fract (θ t) = (z t).1 := congrArg Prod.fst heq
    show (z t).1 = θ t + ((-⌊θ t⌋ : ℤ) : ℝ)
    rw [← h1, Int.fract]; push_cast; ring
  -- continuity modulo `1`
  have hcont : Continuous (fun t => (θ₀ t : AddCircle (1 : ℝ))) := by
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    obtain ⟨θ, c, -, hd, -, hev⟩ := hloc t₀
    have hθc : ContinuousAt (fun t => (θ t : AddCircle (1 : ℝ))) t₀ :=
      (continuous_quotient_mk'.continuousAt).comp hd.continuousAt
    refine hθc.congr ?_
    filter_upwards [hev] with t ht
    obtain ⟨n, hn⟩ := ht
    show (θ t : AddCircle (1 : ℝ)) = (θ₀ t : AddCircle (1 : ℝ))
    rw [hn, ppa_coe_add_int]
  obtain ⟨Θ, hΘc, hΘn⟩ := exists_continuous_lift_of_continuous_mod_one θ₀ hcont
  -- derivative of the lift
  have hder : ∀ t₀, ∃ c : ℝ, c ≠ 0 ∧ HasDerivAt Θ c t₀ := by
    intro t₀
    obtain ⟨θ, c, hc, hd, h0, hev⟩ := hloc t₀
    obtain ⟨n₀, hn₀⟩ := hΘn t₀
    have hC : Θ t₀ - θ t₀ = (n₀ : ℝ) := by rw [hn₀, h0]; ring
    have hD : ContinuousAt (fun t => Θ t - θ t) t₀ := hΘc.continuousAt.sub hd.continuousAt
    have hball : ∀ᶠ t in 𝓝 t₀, dist (Θ t - θ t) (Θ t₀ - θ t₀) < 1 :=
      hD.tendsto.eventually (Metric.ball_mem_nhds _ one_pos)
    have hEq : (fun t => θ t + (n₀ : ℝ)) =ᶠ[𝓝 t₀] Θ := by
      filter_upwards [hev, hball] with t ht hbt
      obtain ⟨m, hm⟩ := ht
      obtain ⟨m', hm'⟩ := hΘn t
      have hk : Θ t - θ t = ((m + m' : ℤ) : ℝ) := by rw [hm', hm]; push_cast; ring
      rw [hk, hC] at hbt
      have := ppa_int_eq _ _ hbt
      show θ t + (n₀ : ℝ) = Θ t
      have h2 : Θ t - θ t = (n₀ : ℝ) := by rw [hk, this]
      linarith
    exact ⟨c, hc, (hd.add_const _).congr_of_eventuallyEq hEq.symm⟩
  choose c' hc'0 hc'd using hder
  refine ⟨Θ, fun t => (z t).2, hΘc, ?_, fun t => ⟨(hz t).2.1, ?_⟩⟩
  · rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (f := Θ) (f' := c') convex_univ
      (fun x _ => (hc'd x).hasDerivWithinAt) (m := 0) (fun x _ => hc'0 x) with h | h
    · exact Or.inr (strictAnti_of_hasDerivAt_neg hc'd fun x => h x (Set.mem_univ x))
    · exact Or.inl (strictMono_of_hasDerivAt_pos hc'd fun x => h x (Set.mem_univ x))
  · obtain ⟨n, hn⟩ := hΘn t
    rw [hn, ppa_page_int page hper]
    exact (hz t).2.2

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H)
    (page : ℝ → Plane → R4)
    (hob : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2) ∧
      (∀ θ u, page (θ + 1) u = page θ u) ∧
      (∀ θ, IsSmoothDiskEmbedding (page θ)) ∧
      (∀ θ, page θ '' closedUnitDisk ⊆ energySurface H) ∧
      (∀ θ t, page θ (circlePoint t) = P.x (P.T * t)) ∧
      (∀ θ, ∀ u ∈ openUnitDisk,
        hamiltonianVectorField H (page θ u) ∉ Set.range (fderiv ℝ (page θ) u)) ∧
      (∀ y ∈ energySurface H, y ∉ P.image →
        ∃! z : ℝ × Plane, z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ openUnitDisk ∧ page z.1 z.2 = y) ∧
      (∀ θ : ℝ, ∀ u ∈ openUnitDisk,
        Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u))))
    (y : ℝ → R4) (hy : IsTrajectory H y) (hy0 : y 0 ∉ P.image) :
    ∃ (Θ : ℝ → ℝ) (u : ℝ → Plane), Continuous Θ ∧ (StrictMono Θ ∨ StrictAnti Θ) ∧
      ∀ t, u t ∈ openUnitDisk ∧ page (Θ t) (u t) = y t :=
  exists_page_parameter_along_trajectory_aux H hS P page hob y hy hy0
