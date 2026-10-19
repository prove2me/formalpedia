-- Prove2me | solution 1 for OAI.Problem356.FiveComponentGeometry.fullConclusion_of_five_component_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:14:06.460744+00:00
-- url     : https://prove2.me/submissions/a5ac9004-3f5e-484f-8838-3f51ca8c94e8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/ActualGeometryConclusion.lean:L33-L184
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.FiveComponentGeometry.fullConclusion_of_five_component_certificate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
import Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombSupportExistence
import Definitions.Def_OAI_Analysis_CoulombTransport_FiveComponentGeometry
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterAxis
import Theorems.Thm_OAI_Problem356_CommonBranches_exists_common_central_ball_in_components
import Theorems.Thm_OAI_Problem356_FiveComponentGeometry_ennreal_local_certificate
import Theorems.Thm_OAI_Problem356_SmoothBranchMarginal_componentRegion_pairwise_of_subsets
import Theorems.Thm_OAI_Problem356_exists_fullCoulombConclusion_of_local_geometry

-- ---- from OAI.Analysis.CoulombTransport.CommonBranches ----
namespace OAI

universe uE uM uIndex uF

/-!
# Reparametrizing local branches by their common central component

For local homeomorphisms `X,Z` on the parameter component, the central
parametrizations are `X.symm` and `X.symm.trans Z`. Their common source is
open, contains the central base point, and inherits both smooth inverses.
-/

noncomputable section
open Set Metric

namespace Problem356.CommonBranches

variable {E : Type uE} [TopologicalSpace E]

/-- The common source permits both the inverse branch and the second outer
branch, with their expected component containment and inverse identity. -/
theorem outer_source_properties (X Z : OpenPartialHomeomorph E E) {x : E}
    (hx : x ∈ (outer X Z).source) :
    x ∈ X.target ∧ X.symm x ∈ X.source ∧ X.symm x ∈ Z.source ∧
      outer X Z x ∈ Z.target ∧ X (X.symm x) = x := by
  change x ∈ X.symm.source ∩ X.symm ⁻¹' Z.source at hx
  exact ⟨hx.1, X.symm.map_source hx.1, hx.2, Z.map_source hx.2,
    X.right_inv hx.1⟩

/-- A common domain for both composed branches is a common domain for all
four outer branches, in the indexing used by the smooth marginal construction. -/
theorem subset_four_sources (X Z : Fin 2 → OpenPartialHomeomorph E E)
    {B : Set E} (hB : ∀ i, B ⊆ (outer (X i) (Z i)).source) :
    ∀ j, B ⊆ (four X Z j).source := by
  intro j
  fin_cases j
  · intro x hx
    exact (outer_source_properties (X 0) (Z 0) (hB 0 hx)).1
  · exact hB 0
  · intro x hx
    exact (outer_source_properties (X 1) (Z 1) (hB 1 hx)).1
  · exact hB 1

section Metric

variable {M : Type uM} [PseudoMetricSpace M]

end Metric

section Smooth

variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smoothness of the inverse central branch and original outer branch
makes the reparametrized branch smooth on its actual open source. -/
theorem contDiffOn_outer {n : WithTop ENat} (X Z : OpenPartialHomeomorph F F)
    (hX : ContDiffOn ℝ n X.symm X.target)
    (hZ : ContDiffOn ℝ n Z Z.source) :
    ContDiffOn ℝ n (outer X Z) (outer X Z).source := by
  exact hZ.comp_inter hX

/-- The inverse of the reparametrized branch is smooth on its actual target. -/
theorem contDiffOn_outer_symm {n : WithTop ENat} (X Z : OpenPartialHomeomorph F F)
    (hX : ContDiffOn ℝ n X X.source)
    (hZ : ContDiffOn ℝ n Z.symm Z.target) :
    ContDiffOn ℝ n (outer X Z).symm (outer X Z).target := by
  exact hX.comp_inter hZ

/-- Forward smoothness of all four centrally parametrized branches. -/
theorem contDiffOn_four {n : WithTop ENat}
    (X Z : Fin 2 → OpenPartialHomeomorph F F)
    (hX : ∀ i, ContDiffOn ℝ n (X i).symm (X i).target)
    (hZ : ∀ i, ContDiffOn ℝ n (Z i) (Z i).source) :
    ∀ j, ContDiffOn ℝ n (four X Z j) (four X Z j).source := by
  intro j
  fin_cases j
  · exact hX 0
  · exact contDiffOn_outer (X 0) (Z 0) (hX 0) (hZ 0)
  · exact hX 1
  · exact contDiffOn_outer (X 1) (Z 1) (hX 1) (hZ 1)

/-- Inverse smoothness of all four centrally parametrized branches. -/
theorem contDiffOn_four_symm {n : WithTop ENat}
    (X Z : Fin 2 → OpenPartialHomeomorph F F)
    (hX : ∀ i, ContDiffOn ℝ n (X i) (X i).source)
    (hZ : ∀ i, ContDiffOn ℝ n (Z i).symm (Z i).target) :
    ∀ j, ContDiffOn ℝ n (four X Z j).symm (four X Z j).target := by
  intro j
  fin_cases j
  · exact hX 0
  · exact contDiffOn_outer_symm (X 0) (Z 0) (hX 0) (hZ 0)
  · exact hX 1
  · exact contDiffOn_outer_symm (X 1) (Z 1) (hX 1) (hZ 1)

end Smooth
end Problem356.CommonBranches

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.ContactSelection ----
namespace OAI

universe uAlpha uIndex

/-! The combinatorial step from a permuted contact triple to branch selection. -/

namespace Problem356
namespace ContactSelection

variable {α : Type uAlpha} {ι : Type uIndex}

/-- If precisely the first source entry belongs to the central set, any
permutation whose first target entry is central has the same first entry. -/
theorem first_eq_of_perm
    {B : Set α} {x y z p q r : α}
    (hperm : List.Perm [x, y, z] [p, q, r])
    (hx : x ∈ B) (hq : q ∉ B) (hr : r ∉ B) : x = p := by
  have hm : x ∈ [p, q, r] := hperm.mem_iff.mp (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hp | hq' | hr'
  · exact hp
  · exact False.elim (hq (hq' ▸ hx))
  · exact False.elim (hr (hr' ▸ hx))

/-- After identifying the central entry, each remaining entry is one of the
other two entries of the contact triple. -/
theorem second_eq_or_third_of_perm
    {B : Set α} {x y z p q r : α}
    (hperm : List.Perm [x, y, z] [p, q, r])
    (hx : x ∈ B) (hq : q ∉ B) (hr : r ∉ B) : y = q ∨ y = r := by
  have hxp := first_eq_of_perm hperm hx hq hr
  subst p
  have hp : List.Perm [y, z] [q, r] := hperm.cons_inv
  have hm : y ∈ [q, r] := hp.mem_iff.mp (by simp)
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hm

/-- A contact triple parameterized by `s`, with central branch `X`,
selects either `Y x` or `W x` once `Y` inverts `X` on the parameter domain. -/
theorem second_selects_inverse_branch
    {B P : Set α} {X Z Y W : α → α} {x y z s : α}
    (hperm : List.Perm [x, y, z] [X s, s, Z s])
    (hx : x ∈ B) (hs : s ∈ P)
    (hOuter : ∀ a ∈ P, a ∉ B ∧ Z a ∉ B)
    (hInverse : ∀ a ∈ P, Y (X a) = a)
    (hW : ∀ a ∈ B, W a = Z (Y a)) : y = Y x ∨ y = W x := by
  have hout := hOuter s hs
  have hcentral := first_eq_of_perm hperm hx hout.1 hout.2
  have hinv : Y x = s := by rw [hcentral]; exact hInverse s hs
  rcases second_eq_or_third_of_perm hperm hx hout.1 hout.2 with hy | hy
  · exact Or.inl (hy.trans hinv.symm)
  · exact Or.inr (hy.trans (by rw [hW x hx, hinv]))

end ContactSelection
end Problem356

end OAI

-- ---- from OAI.Analysis.CoulombTransport.FiveComponentGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open Set Filter Metric
open scoped ENNReal InnerProductSpace

namespace Problem356.FiveComponentGeometry

open LocalGeometry StationaryMap CenterCertificate

lemma point_two_eq_neg : point 2 = -point 1 := by
  change (!₂[-1, 0, 0] : E3) = -(!₂[1, 0, 0] : E3)
  ext i
  fin_cases i <;> norm_num [point]

lemma point_four_eq_neg : point 4 = -point 3 := by
  change (!₂[0, -1, 0] : E3) = -(!₂[0, 1, 0] : E3)
  ext i
  fin_cases i <;> norm_num [point]

end Problem356.FiveComponentGeometry

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.ActualGeometryConclusion ----
namespace OAI

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

namespace Problem356.FiveComponentGeometry

open LocalGeometry CenterCertificate

theorem ennreal_graph_contact {a : E3} (C : ChartsAt a) {s : E3}
    (hs : s ∈ C.charts.central.source)
    (hxy : 0 < dist (C.charts.central s) s)
    (hxz : 0 < dist (C.charts.central s) (C.charts.opposite s))
    (hyz : 0 < dist s (C.charts.opposite s)) :
    ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖C.charts.central s‖ ^ 2) + C.value s +
      ((5 : ℝ) / 4 * ⟪a, C.charts.opposite s + a⟫_ℝ -
        10 * ‖C.charts.opposite s + a‖ ^ 2)) =
      coulombCost (C.charts.central s, (s, C.charts.opposite s)) := by
  have ht := C.charts.mapsTo_state hs
  rw [C.state_ball, ← ball_prod_same] at ht
  exact (ennreal_local_certificate C (C.source_ball ▸ hs) ht.1 ht.2 hxy hxz hyz).2.mpr
    ⟨rfl, rfl⟩

/-- The actual five-component certificate discharges every local-geometry
input, after choosing a sufficiently small common central ball. -/
theorem fullConclusion_of_five_component_certificate
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    (hout₁ : ∀ s ∈ C₁.charts.central.source,
      s ∉ ball (0 : E3) (1 / 4) ∧ C₁.charts.opposite s ∉ ball (0 : E3) (1 / 4))
    (hout₂ : ∀ s ∈ C₂.charts.central.source,
      s ∉ ball (0 : E3) (1 / 4) ∧ C₂.charts.opposite s ∉ ball (0 : E3) (1 / 4))
    {R : ℝ} (hR : 0 < R)
    (hdisj : Pairwise (fun i j : Fin 5 => Disjoint (ball (point i) R) (ball (point j) R)))
    {u : E3 → ℝ} (hu : Measurable u) {M : ℝ} (hM : 0 ≤ M)
    (hubound : ∀ x, |u x| ≤ M)
    (hueq : ∀ i x, x ∈ ball (point i) R → u x = potentials C₁ C₂ i x)
    (hcert : ∀ x ∈ ⋃ i : Fin 5, ball (point i) R,
      ∀ y ∈ ⋃ i : Fin 5, ball (point i) R, ∀ z ∈ ⋃ i : Fin 5, ball (point i) R,
      ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
      (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
        branchContact C₁ C₂ (x, (y, z)))) :
    ∃ rho : E3 → ℝ, HasFullCoulombConclusion rho := by
  let X : Fin 2 → OpenPartialHomeomorph E3 E3 := ![C₁.charts.central, C₂.charts.central]
  let Z : Fin 2 → OpenPartialHomeomorph E3 E3 := ![C₁.charts.opposite, C₂.charts.opposite]
  let a : Fin 2 → E3 := ![point 1, point 3]
  let P : Fin 2 → Set E3 := ![ball (point 1) R, ball (point 3) R]
  let Q : Fin 2 → Set E3 := ![ball (point 2) R, ball (point 4) R]
  have haX : ∀ i, a i ∈ (X i).source := by
    intro i; fin_cases i
    · exact C₁.charts.point_mem
    · exact C₂.charts.point_mem
  have haZ : ∀ i, a i ∈ (Z i).source := by
    intro i; fin_cases i
    · exact C₁.charts.source_eq ▸ C₁.charts.point_mem
    · exact C₂.charts.source_eq ▸ C₂.charts.point_mem
  have hcenter : ∀ i, X i (a i) = 0 := by
    intro i; fin_cases i
    · exact C₁.charts.central_value
    · exact C₂.charts.central_value
  have hP : ∀ i, IsOpen (P i) := by intro i; fin_cases i <;> exact isOpen_ball
  have hQ : ∀ i, IsOpen (Q i) := by intro i; fin_cases i <;> exact isOpen_ball
  have haP : ∀ i, a i ∈ P i := by intro i; fin_cases i <;> exact mem_ball_self hR
  have haQ : ∀ i, Z i (a i) ∈ Q i := by
    intro i; fin_cases i
    · change C₁.charts.opposite (point 1) ∈ ball (point 2) R
      rw [C₁.charts.opposite_value, point_two_eq_neg]
      exact mem_ball_self hR
    · change C₂.charts.opposite (point 3) ∈ ball (point 4) R
      rw [C₂.charts.opposite_value, point_four_eq_neg]
      exact mem_ball_self hR
  obtain ⟨r, hr, hsub, hlocal⟩ := CommonBranches.exists_common_central_ball_in_components
    X Z a 0 haX haZ hcenter P Q hP hQ haP haQ
    (isOpen_ball.inter isOpen_ball)
    (show (0 : E3) ∈ ball 0 R ∩ ball 0 (1 / 4) from
      ⟨mem_ball_self hR, mem_ball_self (by norm_num)⟩)
  let e := CommonBranches.four X Z
  have hBS : ∀ i, ball (0 : E3) r ⊆ (CommonBranches.outer (X i) (Z i)).source :=
    fun i x hx => (hlocal i x hx).1
  have hsource : ∀ i, ball (0 : E3) r ⊆ (e i).source :=
    CommonBranches.subset_four_sources X Z hBS
  have hB0 : ball (0 : E3) r ⊆ ball (point 0) R := by
    have hp0 : point 0 = (0 : E3) := by
      ext i; fin_cases i <;> rfl
    rw [hp0]
    exact fun x hx => (hsub hx).1
  have himages : ∀ i, e i '' ball (0 : E3) r ⊆ ball (point i.succ) R := by
    rintro i _ ⟨x, hx, rfl⟩
    fin_cases i
    · exact (hlocal 0 x hx).2.1
    · exact (hlocal 0 x hx).2.2
    · exact (hlocal 1 x hx).2.1
    · exact (hlocal 1 x hx).2.2
  have he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i) (e i).source := by
    apply CommonBranches.contDiffOn_four
    · intro i; fin_cases i
      · exact C₁.charts.central_inverse_analytic.of_le (by simp)
      · exact C₂.charts.central_inverse_analytic.of_le (by simp)
    · intro i; fin_cases i
      · exact C₁.charts.opposite_analytic.of_le (by simp)
      · exact C₂.charts.opposite_analytic.of_le (by simp)
  have he' : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target := by
    apply CommonBranches.contDiffOn_four_symm
    · intro i; fin_cases i
      · exact C₁.charts.central_analytic.of_le (by simp)
      · exact C₂.charts.central_analytic.of_le (by simp)
    · intro i; fin_cases i
      · exact C₁.charts.opposite_inverse_analytic.of_le (by simp)
      · exact C₂.charts.opposite_inverse_analytic.of_le (by simp)
  have hmem (i : Fin 4) {x : E3} (hx : x ∈ ball (0 : E3) r) :
      e i x ∈ ball (point i.succ) R := himages i ⟨x, hx, rfl⟩
  have hdist {i j : Fin 5} (hij : i ≠ j) {x y : E3}
      (hx : x ∈ ball (point i) R) (hy : y ∈ ball (point j) R) : 0 < dist x y := by
    apply dist_pos.mpr
    intro heq
    exact Set.disjoint_left.mp (hdisj hij) hx (heq ▸ hy)
  have hcontact (i : Fin 2) (x : E3) (hx : x ∈ ball (0 : E3) r) :
      ENNReal.ofReal (u x + u ((X i).symm x) + u (CommonBranches.outer (X i) (Z i) x)) =
        coulombCost (x, ((X i).symm x, CommonBranches.outer (X i) (Z i) x)) := by
    have hprop := CommonBranches.outer_source_properties (X i) (Z i) (hBS i hx)
    fin_cases i
    · change ENNReal.ofReal (u x + u (C₁.charts.central.symm x) +
          u (C₁.charts.opposite (C₁.charts.central.symm x))) =
        coulombCost (x, (C₁.charts.central.symm x, C₁.charts.opposite (C₁.charts.central.symm x)))
      have hy : C₁.charts.central.symm x ∈ ball (point 1) R := hmem 0 hx
      have hz : C₁.charts.opposite (C₁.charts.central.symm x) ∈ ball (point 2) R := hmem 1 hx
      have hinv : C₁.charts.central (C₁.charts.central.symm x) = x := hprop.2.2.2.2
      rw [hueq 0 x (hB0 hx), hueq 1 _ hy, hueq 2 _ hz]
      have hc := ennreal_graph_contact C₁ (s := C₁.charts.central.symm x) hprop.2.1
        (by rw [hinv]; exact hdist (by decide : (0 : Fin 5) ≠ 1) (hB0 hx) hy)
        (by rw [hinv]; exact hdist (by decide : (0 : Fin 5) ≠ 2) (hB0 hx) hz)
        (hdist (by decide : (1 : Fin 5) ≠ 2) hy hz)
      simpa [potentials, hinv] using hc
    · change ENNReal.ofReal (u x + u (C₂.charts.central.symm x) +
          u (C₂.charts.opposite (C₂.charts.central.symm x))) =
        coulombCost (x, (C₂.charts.central.symm x, C₂.charts.opposite (C₂.charts.central.symm x)))
      have hy : C₂.charts.central.symm x ∈ ball (point 3) R := hmem 2 hx
      have hz : C₂.charts.opposite (C₂.charts.central.symm x) ∈ ball (point 4) R := hmem 3 hx
      have hinv : C₂.charts.central (C₂.charts.central.symm x) = x := hprop.2.2.2.2
      rw [hueq 0 x (hB0 hx), hueq 3 _ hy, hueq 4 _ hz]
      have hc := ennreal_graph_contact C₂ (s := C₂.charts.central.symm x) hprop.2.1
        (by rw [hinv]; exact hdist (by decide : (0 : Fin 5) ≠ 3) (hB0 hx) hy)
        (by rw [hinv]; exact hdist (by decide : (0 : Fin 5) ≠ 4) (hB0 hx) hz)
        (hdist (by decide : (3 : Fin 5) ≠ 4) hy hz)
      simpa [potentials, hinv] using hc
  apply exists_fullCoulombConclusion_of_local_geometry 0 hr e hsource
    (SmoothBranchMarginal.componentRegion_pairwise_of_subsets hdisj hB0 himages) he he'
    (MeasurableSet.iUnion fun _ => isOpen_ball.measurableSet)
    (fun x hx => mem_iUnion.mpr ⟨0, hB0 hx⟩)
    (fun i x hx => mem_iUnion.mpr ⟨i.succ, himages i hx⟩)
    hu hM (fun x _ => abs_le.mp (hubound x))
    (fun t h1 h2 h3 => (hcert _ h1 _ h2 _ h3).1)
    (hcontact 0) (hcontact 1)
  intro x y z hx hy hz hc
  have hc' := (hcert x (mem_iUnion.mpr ⟨0, hB0 hx⟩) y hy z hz).2 hc
  rcases hc' with ⟨s, hs, hp⟩ | ⟨s, hs, hp⟩
  · have hy' := ContactSelection.second_selects_inverse_branch hp hx hs
      (fun s hs => ⟨fun h => (hout₁ s hs).1 (hsub h).2,
        fun h => (hout₁ s hs).2 (hsub h).2⟩)
      (fun s hs => C₁.charts.central.left_inv hs)
      (show ∀ w ∈ ball (0 : E3) r,
        CommonBranches.outer C₁.charts.central C₁.charts.opposite w =
          C₁.charts.opposite (C₁.charts.central.symm w) from fun _ _ => rfl)
    rcases hy' with hy' | hy'
    · exact ⟨0, hy'⟩
    · exact ⟨1, hy'⟩
  · have hy' := ContactSelection.second_selects_inverse_branch hp hx hs
      (fun s hs => ⟨fun h => (hout₂ s hs).1 (hsub h).2,
        fun h => (hout₂ s hs).2 (hsub h).2⟩)
      (fun s hs => C₂.charts.central.left_inv hs)
      (show ∀ w ∈ ball (0 : E3) r,
        CommonBranches.outer C₂.charts.central C₂.charts.opposite w =
          C₂.charts.opposite (C₂.charts.central.symm w) from fun _ _ => rfl)
    rcases hy' with hy' | hy'
    · exact ⟨2, hy'⟩
    · exact ⟨3, hy'⟩

end Problem356.FiveComponentGeometry

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.FiveComponentGeometry
open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace
open LocalGeometry CenterCertificate


theorem solution : type_of% @_root_.OAI.Problem356.FiveComponentGeometry.fullConclusion_of_five_component_certificate := @_root_.OAI.Problem356.FiveComponentGeometry.fullConclusion_of_five_component_certificate
