-- Prove2me | solution 1 for OAI.Erdos3.RationalFilteredNilmanifold.exists_scored_native_chart
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T01:27:10.741875+00:00
-- url     : https://prove2.me/submissions/0c5e3829-30ac-4ff9-87f8-755aaf1b458c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1330

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedCutoffs
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped NNReal Manifold ContDiff

variable {ι X : Type*} [Fintype ι]

theorem cutoffCover_sum_ge_one (f : ι → X → ℝ) (hpos : ∀ i x, 0 ≤ f i x)
    (hcover : ∀ x, ∃ i, f i x = 1) (x : X) : 1 ≤ ∑ i, f i x := by
  obtain ⟨i, hi⟩ := hcover x
  rw [← hi]
  exact Finset.single_le_sum (fun j _ => hpos j x) (Finset.mem_univ i)

theorem normalizedCutoffs_range (f : ι → X → ℝ) (hpos : ∀ i x, 0 ≤ f i x)
    (hcover : ∀ x, ∃ i, f i x = 1) (i : ι) (x : X) :
    0 ≤ normalizedCutoffs f i x ∧ normalizedCutoffs f i x ≤ 1 := by
  have hs := cutoffCover_sum_ge_one f hpos hcover x
  refine ⟨div_nonneg (hpos i x) (by linarith), ?_⟩
  apply (div_le_one (by linarith : (0 : ℝ) < ∑ j, f j x)).mpr
  exact Finset.single_le_sum (fun j _ => hpos j x) (Finset.mem_univ i)

theorem sum_normalizedCutoffs (f : ι → X → ℝ) (hpos : ∀ i x, 0 ≤ f i x)
    (hcover : ∀ x, ∃ i, f i x = 1) (x : X) : ∑ i, normalizedCutoffs f i x = 1 := by
  simp only [normalizedCutoffs, ← Finset.sum_div]
  exact div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one (cutoffCover_sum_ge_one f hpos hcover x)))

theorem tsupport_normalizedCutoffs_subset [TopologicalSpace X]
    (f : ι → X → ℝ) (i : ι) : tsupport (normalizedCutoffs f i) ⊆ tsupport (f i) := by
  apply closure_mono
  intro x hx hzero
  exact hx (by simp only [normalizedCutoffs, hzero, zero_div])

theorem lipschitz_normalizedCutoffs [PseudoMetricSpace X]
    (f : ι → X → ℝ) (K : ℝ≥0) (hLip : ∀ i, LipschitzWith K (f i))
    (hrange : ∀ i x, 0 ≤ f i x ∧ f i x ≤ 1) (hcover : ∀ x, ∃ i, f i x = 1) (i : ι) :
    LipschitzWith ((Fintype.card ι + 1) * K) (normalizedCutoffs f i) := by
  have hpos := fun i x => (hrange i x).1
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hdiff (j) : |f j x - f j y| ≤ (K : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using (hLip j).dist_le_mul x y
  have hsum : |(∑ j, f j x) - ∑ j, f j y| ≤ (Fintype.card ι : ℝ) * K * dist x y := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j, |f j x - f j y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ι, (K : ℝ) * dist x y := Finset.sum_le_sum (fun j _ => hdiff j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have h := abs_div_sub_div_bound (r := 1) (by norm_num)
    (cutoffCover_sum_ge_one f hpos hcover x) (cutoffCover_sum_ge_one f hpos hcover y)
    (by positivity) (M := 1) (by norm_num) (by positivity) (hdiff i)
    (by rw [abs_of_nonneg (hrange i y).1]; exact (hrange i y).2) hsum
  rw [Real.dist_eq]
  apply h.trans_eq
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  ring

theorem contMDiff_normalizedCutoffs_comp
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (f : ι → X → ℝ) (q : M → X)
    (hsmooth : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun g => f i (q g)))
    (hpos : ∀ i x, 0 ≤ f i x) (hcover : ∀ x, ∃ i, f i x = 1) (i : ι) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun g => normalizedCutoffs f i (q g)) := by
  apply (hsmooth i).div₀ (ContMDiff.sum (fun j _ => hsmooth j))
  intro g
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (cutoffCover_sum_ge_one f hpos hcover (q g)))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SeparatedCosetBalls
namespace OAI

section

namespace Erdos3

open scoped ENNReal NNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G]

theorem dist_le_dist_mul_of_separated_ball (Γ : Subgroup G) (z : G) (R : ℝ)
    (hsep : ∀ γ ∈ Γ, γ ≠ 1 → 4 * R ≤ dist z (z * γ))
    {x y : G} (hx : dist x z ≤ R) (hy : dist y z ≤ R) (γ : Γ) :
    dist x y ≤ dist x (y * γ) := by
  by_cases hγ : (γ : G) = 1
  · simp only [hγ, mul_one, le_refl]
  · have hs := hsep γ γ.property hγ
    have hchain : dist z (z * γ) ≤ dist z x + dist x (y * γ) + dist (y * γ) (z * γ) :=
      (dist_triangle z x (z * γ)).trans (by linarith [dist_triangle x (y * γ) (z * γ)])
    rw [dist_mul_right] at hchain
    have hxy := dist_triangle x z y
    rw [dist_comm z x] at hchain
    rw [dist_comm z y] at hxy
    linarith

theorem rightCosetEDist_eq_edist_of_separated_ball (Γ : Subgroup G) (z : G) (R : ℝ)
    (hsep : ∀ γ ∈ Γ, γ ≠ 1 → 4 * R ≤ dist z (z * γ))
    {x y : G} (hx : dist x z ≤ R) (hy : dist y z ≤ R) :
    rightCosetEDist Γ x y = edist x y := by
  apply le_antisymm (rightCosetEDist_le Γ x y)
  apply le_iInf
  intro γ
  simp only [edist_dist]
  exact ENNReal.ofReal_le_ofReal (dist_le_dist_mul_of_separated_ball Γ z R hsep hx hy γ)

omit [IsIsometricSMul Gᵐᵒᵖ G] in
theorem separated_ball_of_lipschitz_left (Γ : Subgroup G) {δ R : ℝ} {C : ℝ≥0}
    (hC : 0 < C) (hgap : ∀ γ ∈ Γ, γ ≠ 1 → δ ≤ dist 1 γ)
    (hR : 4 * R * C ≤ δ) (z : G) (hleft : LipschitzWith C (fun x => z⁻¹ * x)) :
    ∀ γ ∈ Γ, γ ≠ 1 → 4 * R ≤ dist z (z * γ) := by
  intro γ hγ hne
  have hLip : dist 1 γ ≤ (C : ℝ) * dist z (z * γ) := by
    simpa only [inv_mul_cancel, inv_mul_cancel_left] using hleft.dist_le_mul z (z * γ)
  have hC' : (0 : ℝ) < C := hC
  have hg := hgap γ hγ hne
  nlinarith

variable [IsTopologicalGroup G]

theorem quotient_dist_eq_of_separated_ball (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
    (z : G) (R : ℝ) (hsep : ∀ γ ∈ Γ, γ ≠ 1 → 4 * R ≤ dist z (z * γ)) :
    letI := rightCosetMetricSpace Γ hΓ
    ∀ {x y : G}, dist x z ≤ R → dist y z ≤ R →
      dist (QuotientGroup.mk x : G ⧸ Γ) (QuotientGroup.mk y) = dist x y := by
  let := rightCosetMetricSpace Γ hΓ
  intro x y hx hy
  have h : edist (QuotientGroup.mk x : G ⧸ Γ) (QuotientGroup.mk y) = edist x y :=
    rightCosetEDist_eq_edist_of_separated_ball Γ z R hsep hx hy
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using congrArg ENNReal.toReal h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ChartCutoff
namespace OAI

section

namespace Erdos3

open _root_.Set
open scoped NNReal

theorem chartCutoff_apply {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (e : OpenPartialHomeomorph E X) (ψ : E → ℝ) {v : E} (hv : v ∈ e.source) :
    chartCutoff e ψ (e v) = ψ v := by
  simp only [chartCutoff, if_pos (e.map_source hv), e.left_inv hv]

theorem tsupport_chartCutoff_subset {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space X] (e : OpenPartialHomeomorph E X) (ψ : E → ℝ) {S : Set E}
    (hS : IsCompact S) (hsource : S ⊆ e.source) (hsupport : Function.support ψ ⊆ S) :
    tsupport (chartCutoff e ψ) ⊆ e '' S := by
  classical
  apply closure_minimal ?_ (hS.image_of_continuousOn (e.continuousOn.mono hsource)).isClosed
  intro x hx
  have hxt : x ∈ e.target := by
    by_contra h
    exact hx (by simp only [chartCutoff, if_neg h])
  refine ⟨e.symm x, hsupport ?_, e.right_inv hxt⟩
  simpa only [Function.mem_support, chartCutoff, if_pos hxt] using hx

theorem hasCompactSupport_chartCutoff {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space X] (e : OpenPartialHomeomorph E X) (ψ : E → ℝ) {S : Set E}
    (hS : IsCompact S) (hsource : S ⊆ e.source) (hsupport : Function.support ψ ⊆ S) :
    HasCompactSupport (chartCutoff e ψ) :=
  (hS.image_of_continuousOn (e.continuousOn.mono hsource)).of_isClosed_subset
    isClosed_closure (tsupport_chartCutoff_subset e ψ hS hsource hsupport)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxChartCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem exists_smooth_box_cutoffs :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∀ {ι : Type*} [Fintype ι] (r : ℝ≥0), 0 < r →
      ∃ ψ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        (∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) ∧
        (∀ v, (∀ i, |v i| ≤ (r : ℝ) / 2) → ψ v = 1) ∧
        (∀ v, (∃ i, 3 * (r : ℝ) / 4 ≤ |v i|) → ψ v = 0) ∧
        LipschitzWith (Fintype.card ι * A / r) ψ := by
  obtain ⟨A, hA, χ, hsmooth, hχ, hone, hzero, hLip⟩ := exists_smooth_scalar_cutoff
  refine ⟨A, hA, ?_⟩
  intro ι _ r hr
  exact ⟨coordinateBoxCutoff χ r, contDiff_coordinateBoxCutoff χ hsmooth r,
    hasCompactSupport_coordinateBoxCutoff χ hzero hr,
    coordinateBoxCutoff_range χ hχ r, coordinateBoxCutoff_eq_one χ hone hr,
    coordinateBoxCutoff_eq_zero χ hzero hr, lipschitz_coordinateBoxCutoff χ A r hr hχ hLip⟩

end Erdos3

end

section

namespace Erdos3

open _root_.Set

theorem support_subset_box_of_cutoff {ι : Type*} [Fintype ι] (ψ : (ι → ℝ) → ℝ)
    {r : ℝ} (hr : 0 < r) (hzero : ∀ v, (∃ i, 3 * r / 4 ≤ |v i|) → ψ v = 0) :
    Function.support ψ ⊆ Metric.closedBall 0 (3 * r / 4) := by
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 3 * r / 4)).mpr
  intro i
  rw [Real.norm_eq_abs]
  by_contra! hi
  exact hv (hzero v ⟨i, hi.le⟩)

theorem boxChartCutoff_support {ι X : Type*} [Fintype ι] [TopologicalSpace X] [T2Space X]
    (φ : OpenPartialHomeomorph (ι → ℝ) X) (ψ : (ι → ℝ) → ℝ) {r : ℝ} (hr : 0 < r)
    (hsource : φ.source = {v | ∀ i, |v i| < r})
    (hzero : ∀ v, (∃ i, 3 * r / 4 ≤ |v i|) → ψ v = 0) :
    HasCompactSupport (chartCutoff φ ψ) ∧ tsupport (chartCutoff φ ψ) ⊆ φ.target := by
  have hS := closedBox_subset_chart_source φ hr hsource
  have hsupport := support_subset_box_of_cutoff ψ hr hzero
  refine ⟨hasCompactSupport_chartCutoff φ ψ (isCompact_closedBall _ _) hS hsupport, ?_⟩
  intro x hx
  obtain ⟨v, hv, rfl⟩ := tsupport_chartCutoff_subset φ ψ (isCompact_closedBall _ _) hS hsupport hx
  exact φ.map_source (hS hv)

theorem boxChartCutoff_eq_one {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (φ : OpenPartialHomeomorph (ι → ℝ) X) (ψ : (ι → ℝ) → ℝ) {r : ℝ} (hr : 0 < r)
    (hsource : φ.source = {v | ∀ i, |v i| < r})
    (hone : ∀ v, (∀ i, |v i| ≤ r / 2) → ψ v = 1) (v : ι → ℝ)
    (hv : ∀ i, |v i| ≤ r / 2) : chartCutoff φ ψ (φ v) = 1 := by
  rw [chartCutoff_apply φ ψ (by rw [hsource]; intro i; linarith [hv i])]
  exact hone v hv

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MetricOpenCharts
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_openPartialHomeomorph_of_metric_bounds
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [Nonempty X]
    (f : X → Y) (hf : Continuous f) (ho : IsOpenMap f) (U : Set X) (hU : IsOpen U) (K : ℝ≥0)
    (hupper : ∀ x ∈ U, ∀ y ∈ U, dist (f x) (f y) ≤ K * dist x y)
    (hlower : ∀ x ∈ U, ∀ y ∈ U, dist x y ≤ K * dist (f x) (f y)) :
    ∃ e : OpenPartialHomeomorph X Y, (∀ x, e x = f x) ∧ e.source = U ∧ e.target = f '' U ∧
      LipschitzOnWith K e e.source ∧ LipschitzOnWith K e.symm e.target := by
  have hinj : Set.InjOn f U := by
    intro x hx y hy hxy
    apply dist_eq_zero.mp
    exact le_antisymm (by simpa only [hxy, dist_self, mul_zero] using hlower x hx y hy) dist_nonneg
  let e := OpenPartialHomeomorph.ofContinuousOpen (hinj.toPartialEquiv f U) hf.continuousOn ho hU
  refine ⟨e, fun _ => rfl, rfl, rfl, ?_, ?_⟩
  · exact LipschitzOnWith.of_dist_le_mul hupper
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := hlower (e.symm x) (e.map_target hx) (e.symm y) (e.map_target hy)
    change dist (e.symm x) (e.symm y) ≤ K * dist (e (e.symm x)) (e (e.symm y)) at h
    simpa only [e.right_inv hx, e.right_inv hy] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHChartCutoffSmooth
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥} [TopologicalSpace L]

section Real

variable [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] [FiniteDimensional ℝ L]

end Real

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable [TopologicalSpace L]

variable [IsTopologicalAddGroup L] [ContinuousSMul ℝ L]

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

variable [IsScalarTower ℚ ℝ L]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

local notation "E" => ℝ ⊗[ℚ] L

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set Manifold
open scoped Manifold ContDiff Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem eventuallyEq_quotient_chartInverse
    (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (z : NilpotentLieBCHGroup L s hnil) (φ : OpenPartialHomeomorph (ι → ℝ) (_ ⧸ Γ))
    (hφ : ∀ v, φ v = QuotientGroup.mk (z * (basisHomeomorph e).symm v))
    (g : NilpotentLieBCHGroup L s hnil) (hg : (QuotientGroup.mk g : _ ⧸ Γ) ∈ φ.target) :
    ∃ γ : Γ, (fun h : NilpotentLieBCHGroup L s hnil => φ.symm (QuotientGroup.mk h)) =ᶠ[𝓝 g]
      (fun h => basisHomeomorph e (z⁻¹ * (h * (γ : NilpotentLieBCHGroup L s hnil)))) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let v := φ.symm (QuotientGroup.mk g)
  let a := z * (basisHomeomorph e).symm v
  have ha : (QuotientGroup.mk a : _ ⧸ Γ) = QuotientGroup.mk g :=
    (hφ v).symm.trans (φ.right_inv hg)
  let γ : Γ := ⟨g⁻¹ * a, QuotientGroup.eq.mp ha.symm⟩
  have hga : g * (γ : NilpotentLieBCHGroup L s hnil) = a := by
    simp only [γ, mul_inv_cancel_left]
  let f := fun h : NilpotentLieBCHGroup L s hnil =>
    basisHomeomorph e (z⁻¹ * (h * (γ : NilpotentLieBCHGroup L s hnil)))
  have hf : Continuous f := (basisHomeomorph e).continuous.comp
    (continuous_const.mul (continuous_id.mul continuous_const))
  have hfg : f g = v := by
    dsimp only [f]
    rw [hga]
    simp only [a, inv_mul_cancel_left, Homeomorph.apply_symm_apply]
  have hnear : ∀ᶠ h in 𝓝 g, f h ∈ φ.source :=
    hf.continuousAt (φ.open_source.mem_nhds (hfg ▸ φ.map_target hg))
  refine ⟨γ, ?_⟩
  filter_upwards [hnear] with h hh
  have hφf : φ (f h) = (QuotientGroup.mk h : _ ⧸ Γ) := by
    rw [hφ]
    dsimp only [f]
    rw [Homeomorph.symm_apply_apply, mul_inv_cancel_left]
    exact quotient_mk_mul_mem Γ h γ
  change φ.symm (QuotientGroup.mk h) = f h
  rw [← hφf, φ.left_inv hh]

theorem contMDiffAt_quotient_chartInverse
    (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (z : NilpotentLieBCHGroup L s hnil) (φ : OpenPartialHomeomorph (ι → ℝ) (_ ⧸ Γ))
    (hφ : ∀ v, φ v = QuotientGroup.mk (z * (basisHomeomorph e).symm v))
    (n : ℕ∞ω) (g : NilpotentLieBCHGroup L s hnil) (hg : (QuotientGroup.mk g : _ ⧸ Γ) ∈ φ.target) :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiffAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n
      (fun h : NilpotentLieBCHGroup L s hnil => φ.symm (QuotientGroup.mk h)) g := by
  let := basisChartedSpace (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e n
  obtain ⟨γ, hγ⟩ := eventuallyEq_quotient_chartInverse e Γ z φ hφ g hg
  have hsmooth : ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n
      (fun h : NilpotentLieBCHGroup L s hnil =>
        basisHomeomorph e (z⁻¹ * (h * (γ : NilpotentLieBCHGroup L s hnil)))) :=
    (contMDiff_basisHomeomorph e n).comp (contMDiff_const.mul (contMDiff_id.mul contMDiff_const))
  exact hsmooth.contMDiffAt.congr_of_eventuallyEq hγ

theorem contDiffOn_quotient_chart_transition
    (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (z w : NilpotentLieBCHGroup L s hnil) (φ ψ : OpenPartialHomeomorph (ι → ℝ) (_ ⧸ Γ))
    (hφ : ∀ v, φ v = QuotientGroup.mk (z * (basisHomeomorph e).symm v))
    (hψ : ∀ v, ψ v = QuotientGroup.mk (w * (basisHomeomorph e).symm v)) (n : ℕ∞ω) :
    ContDiffOn ℝ n (φ.trans ψ.symm) (φ.trans ψ.symm).source := by
  let := basisChartedSpace (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e n
  intro v hv
  have htarget : (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ) ∈ ψ.target := by
    rw [← hφ]
    exact hv.2
  have hi := contMDiffAt_quotient_chartInverse e Γ w ψ hψ n
    (z * (basisHomeomorph e).symm v) htarget
  have hz : ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n
      (fun u : ι → ℝ => z * (basisHomeomorph e).symm u) :=
    contMDiff_const.mul (contMDiff_basisHomeomorph_symm e n)
  have ht := (hi.comp v hz.contMDiffAt).contDiffAt.contDiffWithinAt (s := (φ.trans ψ.symm).source)
  simpa only [Function.comp_def, OpenPartialHomeomorph.coe_trans, hφ] using ht

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set Manifold
open scoped Manifold ContDiff Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem contMDiff_quotient_chartCutoff
    (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (z : NilpotentLieBCHGroup L s hnil)
    (φ : OpenPartialHomeomorph (ι → ℝ) (_ ⧸ Γ))
    (hφ : ∀ v, φ v = QuotientGroup.mk (z * (basisHomeomorph e).symm v))
    (ψ : (ι → ℝ) → ℝ) (hsmooth : ContDiff ℝ ∞ ψ)
    (hsupport : tsupport (chartCutoff φ ψ) ⊆ φ.target) :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun g : NilpotentLieBCHGroup L s hnil => chartCutoff φ ψ (QuotientGroup.mk g)) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := basisChartedSpace (hnil := hnil) e
  apply contMDiff_of_tsupport
  intro g hg
  have hgt : (QuotientGroup.mk g : _ ⧸ Γ) ∈ φ.target :=
    hsupport (tsupport_comp_subset_preimage (chartCutoff φ ψ) QuotientGroup.continuous_mk hg)
  have hi := contMDiffAt_quotient_chartInverse e Γ z φ hφ ∞ g hgt
  have hnear : ∀ᶠ h in 𝓝 g, (QuotientGroup.mk h : _ ⧸ Γ) ∈ φ.target :=
    QuotientGroup.continuous_mk.continuousAt (φ.open_target.mem_nhds hgt)
  apply (hsmooth.contMDiff.contMDiffAt.comp g hi).congr_of_eventuallyEq
  filter_upwards [hnear] with h hh
  exact dif_pos hh

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuantitativeMetricPartition
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

variable {ι : Type*} [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem boxCoverCount_le_exp (C d : ℕ) (hC : 2 ≤ C) (K : ℝ≥0) {B ε p : ℝ}
    (hB0 : 0 ≤ B) (hε : 0 < ε) (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hB : B ≤ Real.exp ((p + C) ^ C)) (hK : (K : ℝ) ≤ Real.exp ((p + C) ^ C))
    (hεinv : 1 / ε ≤ Real.exp ((p + C) ^ C)) :
    (((boxCoverMeshCount B K ε + 1) ^ d : ℕ) : ℝ) ≤
      Real.exp ((p + (C + 5)) ^ (C + 5)) := by
  let t : ℝ := p + (C + 5 : ℕ)
  have ht : 5 ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) C]
  have ht1 : 1 ≤ t := by linarith
  have hpt : p ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) C]
  have hq : (p + C) ^ C ≤ t ^ C :=
    pow_le_pow_left₀ (by positivity) (by dsimp [t]; push_cast; linarith) C
  have hfactor : 3 * (p + C) ^ C + 4 ≤ t ^ (C + 2) := by
    have hpow : 1 ≤ t ^ C := one_le_pow₀ ht1
    have hsquare : 7 ≤ t ^ 2 := by nlinarith
    calc
      _ ≤ 7 * t ^ C := by linarith
      _ ≤ t ^ 2 * t ^ C := mul_le_mul_of_nonneg_right hsquare (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hmesh := boxCoverMeshCount_add_one_le_exp K hB0 hε (by positivity) hB hK hεinv
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (3 * (p + C) ^ C + 4)) ^ d := pow_le_pow_left₀ (by positivity) hmesh d
    _ = Real.exp ((d : ℝ) * (3 * (p + C) ^ C + 4)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (t * t ^ (C + 2)) := Real.exp_le_exp.mpr
      (mul_le_mul (hd.trans hpt) hfactor (by positivity) (by linarith))
    _ = Real.exp (t ^ (C + 3)) := by rw [show C + 3 = (C + 2) + 1 by omega, pow_succ' t (C + 2)]
    _ ≤ Real.exp (t ^ (C + 5)) := Real.exp_le_exp.mpr (pow_le_pow_right₀ ht1 (by omega))
    _ = _ := by simp [t]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem metricPartition_constant_power_budget (C n : ℕ) (hC : 2 ≤ C) (r : ℝ≥0) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ Real.exp ((p + C) ^ C))
    (hr : 1 / (r : ℝ) ≤ Real.exp ((p + C) ^ C)) :
    (((2 * n + 1 : ℝ≥0) / r : ℝ≥0) : ℝ) ≤ Real.exp ((p + (C + 3)) ^ (C + 3)) := by
  apply (metricPartition_constant_le_exp n r (by positivity) hn hr).trans
  apply Real.exp_le_exp.mpr
  let t : ℝ := p + (C + 3 : ℕ)
  have ht : 5 ≤ t := by
    have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp [t]
    push_cast
    linarith
  have hpow : 1 ≤ t ^ C := one_le_pow₀ (by linarith)
  have hq : (p + C) ^ C ≤ t ^ C :=
    pow_le_pow_left₀ (by positivity) (by dsimp [t]; push_cast; linarith) C
  calc
    _ ≤ 4 * t ^ C := by linarith
    _ ≤ t * t ^ C := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = t ^ (C + 1) := (pow_succ' t C).symm
    _ ≤ t ^ (C + 3) := pow_le_pow_right₀ (by linarith) (by omega)
    _ = _ := by simp [t]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHLatticeImageGap
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped ContDiff

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle NNReal ENNReal

section Norm

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Norm

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ⁅ℝ⁆ M)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s t : ℕ} (e : Basis ι ℝ L)
  (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle NNReal ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (v : ι → ℝ)

variable [IsScalarTower ℚ ℝ L]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle NNReal ENNReal

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M)
  (φ : NilpotentLieBCHGroup L s hnil →* NilpotentLieBCHGroup M s hM)
  (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) (hA : homCoordinates e f φ = A)

include hA

variable [IsScalarTower ℚ ℝ L] [IsScalarTower ℚ ℝ M]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped NNReal

namespace NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dist_coordinates_le_bchInverseBoxConstant
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (B : ℝ≥0) (hB : 1 ≤ B) (g h : NilpotentLieBCHGroup L s hnil)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) (hh : ∀ i, |e.repr h.coord i| ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    dist (basisHomeomorph e g) (basisHomeomorph e h) ≤
      bchInverseBoxConstant s (Fintype.card ι) H B * dist g h := by
  let := rightMetricSpace (hnil := hnil) e
  let A := bchBoxCoordinateBound s (Fintype.card ι) H B
  let C := bchLogMetricConstant s (Fintype.card ι) H 1
  have hA : 0 ≤ A := bchBoxCoordinateBound_nonneg _ _ _ B.coe_nonneg
  change dist (basisHomeomorph e g) (basisHomeomorph e h) ≤
    (A + 2 * (B : ℝ)) * (C : ℝ) * dist g h
  by_cases hnear : (C : ℝ) * dist g h < 1
  · let z := h * g⁻¹
    have hdist : dist 1 z = dist g h := by
      simpa only [mul_inv_cancel] using (rightMetricSpace_isometry_mul_right e g⁻¹).dist_eq g h
    have hz : ‖basisHomeomorph e z‖ ≤ (C : ℝ) * dist g h := by
      have hn : (C : ℝ) * dist 1 z < (1 : ℝ≥0) := by simpa only [hdist, NNReal.coe_one] using hnear
      simpa only [hdist] using norm_coordinates_le_of_near_one e c hstructure hc 1 le_rfl z hn
    have hzbox : ∀ i, |basisHomeomorph e z i| ≤ B := by
      intro i
      have hi : |basisHomeomorph e z i| ≤ ‖basisHomeomorph e z‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (basisHomeomorph e z) i
      exact ((hi.trans hz).trans hnear.le).trans hB
    have hzero : basisHomeomorph (hnil := hnil) e 1 = 0 := by
      simp only [basisHomeomorph_apply, coord_one, map_zero]
    have hRzero : rightTranslate e g 0 = basisHomeomorph e g := by
      rw [← hzero, rightTranslate_coordinates, one_mul]
    have hzg : z * g = h := by simp only [z, inv_mul_cancel_right]
    have hLip := (lipschitzOn_rightTranslate_box e c hstructure hc g B hB hg).dist_le_mul
      (basisHomeomorph e z) hzbox 0
      (show ∀ i, |(0 : ι → ℝ) i| ≤ (B : ℝ) by simpa only [Pi.zero_apply, abs_zero] using fun _ : ι => B.coe_nonneg)
    have hfirst : dist (basisHomeomorph e g) (basisHomeomorph e h) ≤ A * ‖basisHomeomorph e z‖ := by
      rw [rightTranslate_coordinates, hzg, hRzero, dist_zero_right] at hLip
      simpa only [NNReal.toReal, dist_comm, A] using hLip
    calc
      _ ≤ A * ‖basisHomeomorph e z‖ := hfirst
      _ ≤ A * ((C : ℝ) * dist g h) := mul_le_mul_of_nonneg_left hz hA
      _ ≤ (A + 2 * (B : ℝ)) * ((C : ℝ) * dist g h) :=
        mul_le_mul_of_nonneg_right (by linarith [B.coe_nonneg]) (by positivity)
      _ = _ := by ring
  · have hdist : dist (basisHomeomorph e g) (basisHomeomorph e h) ≤ 2 * (B : ℝ) := by
      apply (dist_pi_le_iff (by positivity)).mpr
      intro i
      change |e.repr g.coord i - e.repr h.coord i| ≤ _
      exact (abs_sub _ _).trans (by linarith [hg i, hh i])
    calc
      _ ≤ 2 * (B : ℝ) := hdist
      _ ≤ 2 * (B : ℝ) * ((C : ℝ) * dist g h) :=
        le_mul_of_one_le_right (by positivity) (le_of_not_gt hnear)
      _ ≤ (A + 2 * (B : ℝ)) * ((C : ℝ) * dist g h) := by gcongr; linarith
      _ = _ := by ring

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

theorem bchLatticeSeparationRadius_pos (s d H l : ℕ) : 0 < bchLatticeSeparationRadius s d H l := by
  have hC : (0 : ℝ) < bchLogMetricConstant s d H 1 := bchLogMetricConstant_pos _ _ _ _
  unfold bchLatticeSeparationRadius
  positivity

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem eq_one_of_subgroup_of_dist_lt (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l)
    (γ : NilpotentLieBCHGroup L s hnil) (hγ : γ ∈ Γ) :
    letI := rightMetricSpace (hnil := hnil) e
    dist 1 γ < bchLatticeSeparationRadius s (Fintype.card ι) H l → γ = 1 := by
  let := rightMetricSpace (hnil := hnil) e
  intro hsmall
  let C := bchLogMetricConstant s (Fintype.card ι) H 1
  have hC : (0 : ℝ) < C := bchLogMetricConstant_pos _ _ _ _
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hscaled : (C : ℝ) * dist 1 γ < 1 / ((l : ℝ) + 1) := by
    have h := (lt_div_iff₀ hC).mp hsmall
    simpa only [mul_comm] using h
  have hunit : 1 / ((l : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hn := norm_coordinates_le_of_near_one e c hstructure hc 1 le_rfl γ (hscaled.trans_le hunit)
  apply eq_one_of_subgroup_grid_of_small_coordinates e Γ l hl hgrid γ hγ
  intro i
  have hi : |e.repr γ.coord i| ≤ ‖basisHomeomorph e γ‖ := by
    simpa only [basisHomeomorph_apply, Basis.equivFun_apply, Real.norm_eq_abs] using
      norm_le_pi_norm (basisHomeomorph e γ) i
  exact ((hi.trans hn).trans_lt hscaled).trans (one_div_lt_one_div_of_lt hl' (by linarith))

theorem latticeSeparationRadius_le_dist (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l)
    (γ : NilpotentLieBCHGroup L s hnil) (hγ : γ ∈ Γ) (hne : γ ≠ 1) :
    letI := rightMetricSpace (hnil := hnil) e
    bchLatticeSeparationRadius s (Fintype.card ι) H l ≤ dist 1 γ := by
  let := rightMetricSpace (hnil := hnil) e
  by_contra! h
  exact hne (eq_one_of_subgroup_of_dist_lt e c hstructure hc Γ l hl hgrid γ hγ h)

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem one_le_bchLogMetricConstant (s d H : ℕ) (B : ℝ≥0) :
    1 ≤ bchLogMetricConstant s d H B := by
  change (1 : ℝ) ≤ bchBoxCoordinateBound s d H B + 1
  linarith [bchBoxCoordinateBound_nonneg s d H B.coe_nonneg]

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dist_coordinates_le_of_near_unit_box
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (g h : NilpotentLieBCHGroup L s hnil) (hg : ∀ i, |e.repr g.coord i| ≤ 1) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card ι) H 1
    (C : ℝ) * dist g h < 1 →
      dist (basisHomeomorph e g) (basisHomeomorph e h) ≤ (C : ℝ) ^ 2 * dist g h := by
  let := rightMetricSpace (hnil := hnil) e
  let C := bchLogMetricConstant s (Fintype.card ι) H 1
  dsimp only
  intro hnear
  let z := h * g⁻¹
  have hdist : dist 1 z = dist g h := by
    simpa only [mul_inv_cancel] using (rightMetricSpace_isometry_mul_right e g⁻¹).dist_eq g h
  have hz : ‖basisHomeomorph e z‖ ≤ (C : ℝ) * dist g h := by
    have hn : (C : ℝ) * dist 1 z < (1 : ℝ≥0) := by simpa only [hdist, NNReal.coe_one] using hnear
    simpa only [hdist] using norm_coordinates_le_of_near_one e c hstructure hc 1 le_rfl z hn
  have hzbox (i) : |basisHomeomorph e z i| ≤ 1 := by
    have hi : |basisHomeomorph e z i| ≤ ‖basisHomeomorph e z‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (basisHomeomorph e z) i
    exact ((hi.trans hz).trans hnear.le)
  have hzero : basisHomeomorph (hnil := hnil) e 1 = 0 := by
    simp only [basisHomeomorph_apply, coord_one, map_zero]
  have hRzero : rightTranslate e g 0 = basisHomeomorph e g := by
    rw [← hzero, rightTranslate_coordinates, one_mul]
  have hzg : z * g = h := by simp only [z, inv_mul_cancel_right]
  have hLip := (lipschitzOn_rightTranslate_box e c hstructure hc g 1 le_rfl hg).dist_le_mul
    (basisHomeomorph e z) hzbox 0 (by simp)
  rw [rightTranslate_coordinates, hzg, hRzero, dist_zero_right] at hLip
  have hAC : bchBoxCoordinateBound s (Fintype.card ι) H 1 ≤ (C : ℝ) := by
    change bchBoxCoordinateBound s (Fintype.card ι) H 1 ≤ bchBoxCoordinateBound s (Fintype.card ι) H 1 + 1
    linarith
  calc
    _ ≤ bchBoxCoordinateBound s (Fintype.card ι) H 1 * ‖basisHomeomorph e z‖ := by
      simpa only [dist_comm, NNReal.toReal] using hLip
    _ ≤ (C : ℝ) * ‖basisHomeomorph e z‖ := mul_le_mul_of_nonneg_right hAC (norm_nonneg _)
    _ ≤ (C : ℝ) * ((C : ℝ) * dist g h) := mul_le_mul_of_nonneg_left hz C.coe_nonneg
    _ = _ := by ring

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Matrix NNReal

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Matrix NNReal

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

local notation "E" => ℝ ⊗[ℚ] L

section Topology

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end Topology

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

local notation "E" => ℝ ⊗[ℚ] L

section Topology

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end Topology

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]


end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

namespace NilpotentLieBCHGroup

variable {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

namespace NilpotentLieBCHGroup

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ⁅ℝ⁆ M)

variable (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (Λ : Subgroup (NilpotentLieBCHGroup M t hM))
  (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
  (hΛ : IsClosed (Λ : Set (NilpotentLieBCHGroup M t hM)))
  (hmap : Γ ≤ Λ.comap (mapReal φ))

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

section Distance

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Distance

section Map

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

end Map

section BasisChange

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end BasisChange

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (a : NilpotentLieBCHGroup L s hnil)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct NNReal

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

variable (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)

variable (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (Λ : Subgroup (NilpotentLieBCHGroup M t hM)) (hφ : Γ ≤ Λ.comap (mapOfSteps φ))

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem quotient_dist_eq_on_ball_of_lattice_grid
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l) :
    letI := rightMetricSpace (hnil := hnil) e
    ∀ (C : ℝ≥0), 0 < C → ∀ z : NilpotentLieBCHGroup L s hnil,
      LipschitzWith C (fun x => z⁻¹ * x) →
      letI := quotientMetricSpace e Γ hΓ
      ∀ {x y : NilpotentLieBCHGroup L s hnil},
        dist x z ≤ bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * C) →
        dist y z ≤ bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * C) →
        dist (QuotientGroup.mk x : _ ⧸ Γ) (QuotientGroup.mk y) = dist x y := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  intro C hC z hleft
  have hC' : (0 : ℝ) < C := hC
  have hgap := fun γ hγ hne => latticeSeparationRadius_le_dist e c hstructure hc Γ l hl hgrid γ hγ hne
  apply quotient_dist_eq_of_separated_ball Γ hΓ z _
  apply separated_ball_of_lipschitz_left Γ hC hgap ?_ z hleft
  have heq : 4 * (bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * (C : ℝ))) * C =
      bchLatticeSeparationRadius s (Fintype.card ι) H l := by
    field_simp
  exact heq.le

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSmoothChartPartition
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem ball_subset_quotient_coordinate_image
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) :
    letI := rightMetricSpace (hnil := hnil) e
    ∀ C : ℝ≥0, 0 < C → ∀ z : NilpotentLieBCHGroup L s hnil,
      LipschitzWith C (fun x => z⁻¹ * x) → ∀ r : ℝ, 0 < r → r ≤ 1 →
        letI := quotientMetricSpace e Γ hΓ
        let M := C * (bchLogMetricConstant s (Fintype.card ι) H 1) ^ 2
        let q := fun u => (QuotientGroup.mk (z * (basisHomeomorph e).symm u) : _ ⧸ Γ)
        ∀ v : ι → ℝ, (∀ i, |v i| ≤ 3 * r / 4) →
          Metric.ball (q v) (r / (4 * (M : ℝ))) ⊆ q '' {u | ∀ i, |u i| < r} := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  intro C hC z hleft r hr hr1
  let := quotientMetricSpace e Γ hΓ
  dsimp only
  intro v hv x hx
  let C₀ := bchLogMetricConstant s (Fintype.card ι) H 1
  let M : ℝ≥0 := C * C₀ ^ 2
  have hC' : (0 : ℝ) < C := hC
  have hC₀ : (1 : ℝ) ≤ C₀ := one_le_bchLogMetricConstant _ _ _ _
  have hM : (0 : ℝ) < M := by
    change 0 < (C : ℝ) * (C₀ : ℝ) ^ 2
    positivity
  obtain ⟨g, hg, hquot⟩ := rightCosetMetricSpace_exists_lift Γ hΓ
    (z * (basisHomeomorph e).symm v) (r / (4 * (M : ℝ))) x hx
  let a := (basisHomeomorph (hnil := hnil) e).symm v
  let b := z⁻¹ * g
  have hab : dist a b ≤ (C : ℝ) * dist g (z * a) := by
    have ht := hleft.dist_le_mul (z * a) g
    simpa only [inv_mul_cancel_left, dist_comm] using ht
  have hsmall : (C₀ : ℝ) ^ 2 * dist a b < r / 4 := by
    calc
      _ ≤ (C₀ : ℝ) ^ 2 * ((C : ℝ) * dist g (z * a)) :=
        mul_le_mul_of_nonneg_left hab (sq_nonneg _)
      _ = (M : ℝ) * dist g (z * a) := by simp only [M, NNReal.coe_mul, NNReal.coe_pow]; ring
      _ < r / 4 := by
        have ht := (lt_div_iff₀ (by positivity : 0 < 4 * (M : ℝ))).mp hg
        apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
        nlinarith
  have hnear : (C₀ : ℝ) * dist a b < 1 := by
    have hsq : (C₀ : ℝ) ≤ (C₀ : ℝ) ^ 2 := by nlinarith
    have ht := (mul_le_mul_of_nonneg_right hsq (dist_nonneg (x := a) (y := b))).trans_lt hsmall
    linarith
  have ha (i) : |e.repr a.coord i| ≤ 1 := by
    change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph e).symm v) i| ≤ 1
    rw [Homeomorph.apply_symm_apply]
    linarith [hv i]
  have hcoords := dist_coordinates_le_of_near_unit_box e c hstructure hc a b ha hnear
  have hav : basisHomeomorph e a = v := Homeomorph.apply_symm_apply _ v
  rw [hav] at hcoords
  have hu : ∀ i, |basisHomeomorph e b i| < r := by
    intro i
    have hi := dist_le_pi_dist (basisHomeomorph e a) (basisHomeomorph e b) i
    rw [hav, Real.dist_eq] at hi
    have hb := abs_sub_abs_le_abs_sub (basisHomeomorph e b i) (v i)
    rw [abs_sub_comm] at hb
    have ht := (hi.trans hcoords).trans_lt hsmall
    linarith [hv i]
  refine ⟨basisHomeomorph e b, hu, ?_⟩
  change (QuotientGroup.mk (z * (basisHomeomorph e).symm (basisHomeomorph e b)) : _ ⧸ Γ) = x
  rw [Homeomorph.symm_apply_apply]
  simpa only [b, mul_inv_cancel_left] using hquot

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem lipschitz_quotient_chartCutoff
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) :
    letI := rightMetricSpace (hnil := hnil) e
    ∀ C : ℝ≥0, 0 < C → ∀ z : NilpotentLieBCHGroup L s hnil,
      LipschitzWith C (fun x => z⁻¹ * x) → ∀ r : ℝ≥0, 0 < r → r ≤ 1 →
        letI := quotientMetricSpace e Γ hΓ
        ∀ φ : OpenPartialHomeomorph (ι → ℝ) (_ ⧸ Γ),
          (∀ v, φ v = QuotientGroup.mk (z * (basisHomeomorph e).symm v)) →
          φ.source = {v | ∀ i, |v i| < (r : ℝ)} →
          ∀ (ψ : (ι → ℝ) → ℝ) (A K : ℝ≥0),
            (∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) →
            (∀ v, (∃ i, 3 * (r : ℝ) / 4 ≤ |v i|) → ψ v = 0) →
            LipschitzWith A ψ → LipschitzOnWith K φ.symm φ.target →
            LipschitzWith (A * K + 1 / (r / (4 * (C * bchLogMetricConstant s (Fintype.card ι) H 1 ^ 2))))
              (chartCutoff φ ψ) := by
  let := rightMetricSpace (hnil := hnil) e
  intro C hC z hleft r hr hr1
  let := quotientMetricSpace e Γ hΓ
  intro φ hφ hsource ψ A K hψ hzero hLip hInv
  let M := C * bchLogMetricConstant s (Fintype.card ι) H 1 ^ 2
  let δ : ℝ≥0 := r / (4 * M)
  have hδ : 0 < δ := by
    exact div_pos hr (mul_pos (by norm_num) (mul_pos hC (pow_pos (bchLogMetricConstant_pos _ _ _ _) _)))
  apply lipschitz_chartCutoff φ ψ A K δ hδ hψ hLip hInv
  intro x hx hn y hy
  have hv (i) : |φ.symm x i| ≤ 3 * (r : ℝ) / 4 := by
    by_contra! hi
    exact hn (hzero _ ⟨i, hi.le⟩)
  have hball := ball_subset_quotient_coordinate_image e c hstructure hc Γ hΓ C hC z hleft
    r hr hr1 (φ.symm x) hv
  have heqx : (QuotientGroup.mk (z * (basisHomeomorph e).symm (φ.symm x)) : _ ⧸ Γ) = x :=
    (hφ _).symm.trans (φ.right_inv hx)
  dsimp only at hball
  rw [heqx] at hball
  by_contra! hd
  have hyball : y ∈ Metric.ball x ((r : ℝ) / (4 * (M : ℝ))) := by
    simpa only [Metric.mem_ball, dist_comm, δ, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat] using hd
  obtain ⟨u, hu, heq⟩ := hball hyball
  apply hy
  have hus : u ∈ φ.source := by rwa [hsource]
  have hym : φ u = y := (hφ u).trans heq
  exact hym ▸ φ.map_source hus

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal Manifold ContDiff

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_smooth_quotient_chart_partition
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) :
    letI := rightMetricSpace (hnil := hnil) e
    ∀ C : ℝ≥0, 0 < C → ∀ centers : κ → NilpotentLieBCHGroup L s hnil,
      (∀ j, LipschitzWith C (fun x => (centers j)⁻¹ * x)) →
      ∀ r : ℝ≥0, 0 < r → r ≤ 1 →
        letI := quotientMetricSpace e Γ hΓ
        letI := basisChartedSpace (hnil := hnil) e
        ∀ (φ : κ → OpenPartialHomeomorph (ι → ℝ) (_ ⧸ Γ)) (K : ℝ≥0),
          (∀ j v, φ j v = QuotientGroup.mk (centers j * (basisHomeomorph e).symm v)) →
          (∀ j, (φ j).source = {v | ∀ i, |v i| < (r : ℝ)}) →
          (∀ j, LipschitzOnWith K (φ j).symm (φ j).target) →
          (∀ x, ∃ j v, (∀ i, |v i| ≤ (r : ℝ) / 2) ∧ φ j v = x) →
          ∀ (ψ : (ι → ℝ) → ℝ) (A : ℝ≥0), ContDiff ℝ ∞ ψ →
            (∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) →
            (∀ v, (∀ i, |v i| ≤ (r : ℝ) / 2) → ψ v = 1) →
            (∀ v, (∃ i, 3 * (r : ℝ) / 4 ≤ |v i|) → ψ v = 0) → LipschitzWith A ψ →
            let Q := (Fintype.card κ + 1) *
              (A * K + 1 / (r / (4 * (C * bchLogMetricConstant s (Fintype.card ι) H 1 ^ 2))))
            ∃ f : κ → (_ ⧸ Γ) → ℝ,
              (∀ j x, 0 ≤ f j x ∧ f j x ≤ 1) ∧ (∀ x, ∑ j, f j x = 1) ∧
              (∀ j, HasCompactSupport (f j) ∧ tsupport (f j) ⊆ (φ j).target) ∧
              (∀ j, ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ℝ) ∞
                (fun g : NilpotentLieBCHGroup L s hnil => f j (QuotientGroup.mk g))) ∧
              (∀ j, LipschitzWith Q (f j)) ∧
              (∀ j, tsupport (f j) ⊆ φ j '' Metric.closedBall 0 (3 * (r : ℝ) / 4)) := by
  let := rightMetricSpace (hnil := hnil) e
  intro C hC centers hleft r hr hr1
  let := quotientMetricSpace e Γ hΓ
  let := basisChartedSpace (hnil := hnil) e
  intro φ K hφ hsource hInv hcover ψ A hsmooth hrange hone hzero hLip
  dsimp only
  let g := fun j => chartCutoff (φ j) ψ
  have hgpos (j) (x) : 0 ≤ g j x := (chartCutoff_range (φ j) ψ hrange x).1
  have hgrange (j) (x) : 0 ≤ g j x ∧ g j x ≤ 1 := chartCutoff_range (φ j) ψ hrange x
  have hgcover (x) : ∃ j, g j x = 1 := by
    obtain ⟨j, v, hv, rfl⟩ := hcover x
    exact ⟨j, boxChartCutoff_eq_one (φ j) ψ hr (hsource j) hone v hv⟩
  have hgsupport (j) : HasCompactSupport (g j) ∧ tsupport (g j) ⊆ (φ j).target :=
    boxChartCutoff_support (φ j) ψ hr (hsource j) hzero
  have hgsmooth (j) : ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : NilpotentLieBCHGroup L s hnil => g j (QuotientGroup.mk x)) :=
    contMDiff_quotient_chartCutoff e Γ (centers j) (φ j) (hφ j) ψ hsmooth (hgsupport j).2
  have hgLip (j) := lipschitz_quotient_chartCutoff e c hstructure hc Γ hΓ C hC
    (centers j) (hleft j) r hr hr1 (φ j) (hφ j) (hsource j) ψ A K hrange hzero hLip (hInv j)
  refine ⟨normalizedCutoffs g, normalizedCutoffs_range g hgpos hgcover,
    sum_normalizedCutoffs g hgpos hgcover, ?_, ?_, ?_, ?_⟩
  · intro j
    have hs := tsupport_normalizedCutoffs_subset g j
    exact ⟨(hgsupport j).1.of_isClosed_subset isClosed_closure hs, hs.trans (hgsupport j).2⟩
  · exact fun j => contMDiff_normalizedCutoffs_comp g QuotientGroup.mk hgsmooth hgpos hgcover j
  · exact fun j => lipschitz_normalizedCutoffs g _ hgLip hgrange hgcover j
  · intro j
    exact (tsupport_normalizedCutoffs_subset g j).trans
      (tsupport_chartCutoff_subset (φ j) ψ (isCompact_closedBall _ _)
        (closedBox_subset_chart_source (φ j) hr (hsource j))
        (support_subset_box_of_cutoff ψ hr hzero))

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (v : ι → ℝ)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped NNReal

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H : ℕ}
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)

include hstructure hc

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module

namespace NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable [IsScalarTower ℚ ℝ L] {ι : Type*} [Fintype ι] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

namespace NilpotentLieBCHGroup

open Module

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_bch_partition_input_exp_bound (s a C₀ : ℕ) (hC₀ : 2 ≤ C₀) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d H : ℕ) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      let B : ℝ≥0 := ⟨Real.exp ((p + C₀) ^ C₀), Real.exp_nonneg _⟩
      (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      (bchBoxMetricConstant s d H B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      Real.exp ((p + 2) ^ a) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C₁, hC₁, hchart⟩ := exists_bchBoxMetricConstant_exp_bound s C₀
  let C := C₀ + C₁ + a + 4
  have hC : 2 ≤ C := by dsimp [C]; omega
  refine ⟨C, hC, ?_⟩
  intro d H p hp hd hH
  dsimp only
  have hBp := shifted_power_self_mono (C := C₀) (D := C) hp
    (by omega) (by dsimp [C]; omega)
  refine ⟨Real.exp_le_exp.mpr hBp, ?_, ?_⟩
  · have hKr := hchart d H ⟨Real.exp ((p + C₀) ^ C₀), Real.exp_nonneg _⟩ (p + C₀)
      (by positivity) (hd.trans (by linarith [Nat.cast_nonneg (α := ℝ) C₀]))
      (hH.trans (Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) C₀])))
      (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) C₀))
    apply hKr.trans
    apply Real.exp_le_exp.mpr
    have hbase : p + C₀ + C₁ ≤ p + C := by
      have h : (C₀ : ℝ) + C₁ ≤ C := by
        exact_mod_cast (show C₀ + C₁ ≤ C by dsimp [C]; omega)
      linarith
    apply (pow_le_pow_left₀ (by positivity) hbase C₁).trans
    have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
    exact pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  · apply Real.exp_le_exp.mpr
    have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
    apply (pow_le_pow_left₀ (by linarith) (show p + 2 ≤ p + C by linarith) a).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)

end Erdos3

end

section

namespace Erdos3

theorem inverse_radius_product_exp_bound {A l q : ℝ} (hA : 0 ≤ A)
    (hq : 0 ≤ q) (hAq : A ≤ Real.exp q) (hlq : l ≤ Real.exp q) :
    4 * (l + 1) * (A + 1) ≤ Real.exp (2 * q + 16) := by
  have h1 := Real.one_le_exp hq
  have h16 : (16 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  calc
    _ ≤ 4 * (2 * Real.exp q) * (2 * Real.exp q) := by gcongr <;> linarith
    _ = 16 * Real.exp (2 * q) := by rw [show 2 * q = q + q by ring, Real.exp_add]; ring
    _ ≤ Real.exp 16 * Real.exp (2 * q) := mul_le_mul_of_nonneg_right h16 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

namespace NilpotentLieBCHGroup

open Module

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem bchLogMetricConstant_le_inverseBoxConstant (s d H : ℕ) :
    bchLogMetricConstant s d H 1 ≤ bchInverseBoxConstant s d H 1 := by
  change bchBoxCoordinateBound s d H 1 + 1 ≤
    (bchBoxCoordinateBound s d H 1 + 2 * (1 : ℝ)) * (bchBoxCoordinateBound s d H 1 + 1)
  have := bchBoxCoordinateBound_nonneg s d H (B := 1) (by norm_num)
  nlinarith

theorem smooth_partition_cost_le_exp (n d : ℕ) (A K C B r : ℝ≥0) {q : ℝ}
    (hq : 0 ≤ q) (hn : (n : ℝ) ≤ Real.exp q) (hd : (d : ℝ) ≤ Real.exp q)
    (hA : (A : ℝ) ≤ Real.exp q) (hK : (K : ℝ) ≤ Real.exp q)
    (hC : (C : ℝ) ≤ Real.exp q) (hB : (B : ℝ) ≤ Real.exp q)
    (hr : 1 / (r : ℝ) ≤ Real.exp q) :
    (((n + 1) * ((d * A / r) * K + 1 / (r / (4 * (C * B ^ 2))))) : ℝ≥0) ≤
      Real.exp (5 * q + 16) := by
  have h1 : (d : ℝ) * A / r * K ≤ Real.exp q ^ 4 := by
    calc
      _ = (d : ℝ) * A * (1 / r) * K := by ring
      _ ≤ Real.exp q * Real.exp q * Real.exp q * Real.exp q := by gcongr
      _ = _ := by ring
  have h2 : 1 / ((r : ℝ) / (4 * ((C : ℝ) * (B : ℝ) ^ 2))) ≤ 4 * Real.exp q ^ 4 := by
    calc
      _ = 4 * ((C : ℝ) * ((B : ℝ) * B) * (1 / r)) := by rw [one_div_div]; ring
      _ ≤ 4 * (Real.exp q * (Real.exp q * Real.exp q) * Real.exp q) := by gcongr
      _ = _ := by ring
  have hn1 : (n : ℝ) + 1 ≤ 2 * Real.exp q := by linarith [Real.one_le_exp hq]
  change ((n : ℝ) + 1) * ((d : ℝ) * A / r * K + 1 / ((r : ℝ) / (4 * ((C : ℝ) * (B : ℝ) ^ 2)))) ≤ _
  calc
    _ ≤ (2 * Real.exp q) * (Real.exp q ^ 4 + 4 * Real.exp q ^ 4) := by gcongr
    _ = 10 * Real.exp q ^ 5 := by ring
    _ = 10 * Real.exp (5 * q) := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ Real.exp 16 * Real.exp (5 * q) := by
      apply mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
      linarith [Real.add_one_le_exp (16 : ℝ)]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem smooth_partition_power_budget (T n d : ℕ) (hT : 2 ≤ T)
    (A K C B r : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ Real.exp ((p + T) ^ T)) (hd : (d : ℝ) ≤ Real.exp ((p + T) ^ T))
    (hA : (A : ℝ) ≤ Real.exp ((p + T) ^ T)) (hK : (K : ℝ) ≤ Real.exp ((p + T) ^ T))
    (hC : (C : ℝ) ≤ Real.exp ((p + T) ^ T)) (hB : (B : ℝ) ≤ Real.exp ((p + T) ^ T))
    (hr : 1 / (r : ℝ) ≤ Real.exp ((p + T) ^ T)) :
    (((n + 1) * ((d * A / r) * K + 1 / (r / (4 * (C * B ^ 2))))) : ℝ≥0) ≤
      Real.exp ((p + (T + 21 : ℕ)) ^ (T + 21)) := by
  apply (smooth_partition_cost_le_exp n d A K C B r (by positivity) hn hd hA hK hC hB hr).trans
  apply Real.exp_le_exp.mpr
  let t : ℝ := p + (T + 21 : ℕ)
  have ht : 21 ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) T]
  have hpow : 1 ≤ t ^ T := one_le_pow₀ (by linarith)
  have hq : (p + T) ^ T ≤ t ^ T :=
    pow_le_pow_left₀ (by positivity) (by dsimp [t]; push_cast; linarith) T
  calc
    _ ≤ 21 * t ^ T := by linarith
    _ ≤ t * t ^ T := mul_le_mul_of_nonneg_right ht (by positivity)
    _ = t ^ (T + 1) := (pow_succ' t T).symm
    _ ≤ t ^ (T + 21) := pow_le_pow_right₀ (by linarith) (by omega)
    _ = _ := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeMetricGapBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_bchLatticeSeparationRadius_inv_exp_bound (s : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ (d H l : ℕ) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      1 / bchLatticeSeparationRadius s d H l ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hmetric⟩ := exists_bchBoxMetricConstant_exp_bound s 0
  refine ⟨C + 5, by omega, ?_⟩
  intro d H l p hp hd hH hl
  have hunit : ((1 : ℝ≥0) : ℝ) ≤ Real.exp ((p + 2) ^ 0) := by
    simpa only [NNReal.coe_one, pow_zero] using Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
  have hA := bchBoxCoordinateBound_nonneg s d H (B := 1) (by norm_num)
  have hAq := (bchBoxCoordinateBound_le_bchBoxMetricConstant s d H 1).trans
    (hmetric d H 1 p hp hd hH hunit)
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hpq : p ≤ (p + C) ^ C := by
    apply (show p ≤ p + C by linarith).trans
    simpa only [pow_one] using
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + C) (by omega : 1 ≤ C)
  have hprod := inverse_radius_product_exp_bound hA (by positivity : 0 ≤ (p + C) ^ C)
    hAq (hl.trans (Real.exp_le_exp.mpr hpq))
  calc
    1 / bchLatticeSeparationRadius s d H l =
        ((l : ℝ) + 1) * (bchBoxCoordinateBound s d H 1 + 1) := by
      simp only [bchLatticeSeparationRadius, bchLogMetricConstant, NNReal.toReal]
      field_simp
      norm_num
    _ ≤ 4 * ((l : ℝ) + 1) * (bchBoxCoordinateBound s d H 1 + 1) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ l + 1 by positivity) (by linarith : 0 ≤ bchBoxCoordinateBound s d H 1 + 1)]
    _ ≤ Real.exp (2 * (p + C) ^ C + 16) := hprod
    _ ≤ _ := Real.exp_le_exp.mpr (enlarged_power_dominates_twice_add_sixteen hp C hC)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuotientCoordinateRadius
namespace OAI

section

namespace Erdos3

theorem quotientCoordinateRadius_pos {δ K : ℝ} (hδ : 0 < δ) (d : ℕ) :
    0 < quotientCoordinateRadius δ K d := by
  unfold quotientCoordinateRadius
  positivity

theorem quotientCoordinateRadius_le_one {δ K : ℝ} (hδ : 0 < δ) (d : ℕ) :
    quotientCoordinateRadius δ K d ≤ 1 := by
  unfold quotientCoordinateRadius
  apply (div_le_one (by positivity)).mpr
  nlinarith [sq_nonneg K, Nat.cast_nonneg (α := ℝ) d,
    mul_nonneg (sq_nonneg K) (show (0 : ℝ) ≤ d + 1 by positivity)]

theorem quotientCoordinateRadius_small {δ K : ℝ} (hδ : 0 < δ) (d : ℕ) :
    4 * K ^ 2 * (d + 1) * quotientCoordinateRadius δ K d ≤ δ := by
  unfold quotientCoordinateRadius
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [sq_nonneg δ]

theorem quotientCoordinateRadius_inverse {δ K : ℝ} (hδ : 0 < δ) (d : ℕ) :
    1 / quotientCoordinateRadius δ K d = 1 + 4 * K ^ 2 * (d + 1) * (1 / δ) := by
  unfold quotientCoordinateRadius
  field_simp

theorem quotientCoordinateRadius_inverse_power_budget (A B : ℕ) (hA : 2 ≤ A) (hB : 2 ≤ B)
    {δ K p : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hp : 0 ≤ p) (d : ℕ) (hd : (d : ℝ) ≤ p)
    (hδp : 1 / δ ≤ Real.exp ((p + A) ^ A)) (hKp : K ≤ Real.exp ((p + B) ^ B)) :
    1 / quotientCoordinateRadius δ K d ≤ Real.exp ((p + (A + B + 3 : ℕ)) ^ (A + B + 3)) := by
  let C := A + B
  let q := (p + C) ^ C
  have hC : 2 ≤ C := by dsimp [C]; omega
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqδ : 1 / δ ≤ Real.exp q := hδp.trans (Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := A) (D := C) hp (by omega) (by dsimp [C]; omega)))
  have hqK : K ≤ Real.exp q := hKp.trans (Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := B) (D := C) hp (by omega) (by dsimp [C]; omega)))
  have hpq : p + 1 ≤ q := by
    simpa only [Nat.cast_one, pow_one] using
      shifted_power_self_mono (C := 1) (D := C) hp le_rfl (by omega)
  have hdim : (d : ℝ) + 1 ≤ Real.exp q := by linarith [Real.add_one_le_exp q]
  have hproduct : K ^ 2 * ((d : ℝ) + 1) * (1 / δ) ≤ Real.exp (4 * q) := by
    calc
      _ ≤ (Real.exp q) ^ 2 * Real.exp q * Real.exp q := by gcongr
      _ = (Real.exp q) ^ 4 := by ring
      _ = _ := (Real.exp_nat_mul q 4).symm
  have hfive : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hbasic : 1 / quotientCoordinateRadius δ K d ≤ Real.exp (4 * q + 4) := by
    rw [quotientCoordinateRadius_inverse hδ]
    calc
      _ ≤ 5 * Real.exp (4 * q) := by nlinarith [Real.one_le_exp (show 0 ≤ 4 * q by positivity)]
      _ ≤ Real.exp 4 * Real.exp (4 * q) := mul_le_mul_of_nonneg_right hfive (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply hbasic.trans
  apply Real.exp_le_exp.mpr
  let t : ℝ := p + (C + 3 : ℕ)
  have ht : 5 ≤ t := by
    have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp [t]
    push_cast
    linarith
  have hpow : 1 ≤ t ^ C := one_le_pow₀ (by linarith)
  have hqt : q ≤ t ^ C := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [t]
    push_cast
    linarith
  calc
    4 * q + 4 ≤ 8 * t ^ C := by linarith
    _ ≤ t ^ 2 * t ^ C := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = t ^ (C + 2) := by rw [← pow_add, Nat.add_comm]
    _ ≤ t ^ (C + 3) := pow_le_pow_right₀ (by linarith) (by omega)

theorem product_two_power_bounds (A : ℕ) (hA : 2 ≤ A) {x y p : ℝ}
    (hy : 0 ≤ y) (hp : 0 ≤ p)
    (hx : x ≤ Real.exp ((p + A) ^ A)) (hyb : y ≤ Real.exp ((p + A) ^ A)) :
    x * y ≤ Real.exp ((p + (A + 5 : ℕ)) ^ (A + 5)) := by
  calc
    x * y ≤ Real.exp ((p + A) ^ A) * Real.exp ((p + A) ^ A) :=
      mul_le_mul hx hyb hy (Real.exp_nonneg _)
    _ = Real.exp (2 * (p + A) ^ A) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (2 * (p + A) ^ A + 16) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := Real.exp_le_exp.mpr (enlarged_power_dominates_twice_add_sixteen hp A hA)

theorem quotient_chart_parameter_budget (A B E F : ℕ)
    (hA : 2 ≤ A) (hB : 2 ≤ B) (hE : 2 ≤ E) (hF : 2 ≤ F)
    {δ C U V p : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hp : 0 ≤ p) (d : ℕ) (hd : (d : ℝ) ≤ p)
    (hδp : 1 / δ ≤ Real.exp ((p + A) ^ A)) (hCp : C ≤ Real.exp ((p + B) ^ B))
    (hUp : U ≤ Real.exp ((p + E) ^ E)) (hVp : V ≤ Real.exp ((p + F) ^ F)) :
    let D := A + B + E + F + 10
    1 / quotientCoordinateRadius δ C d ≤ Real.exp ((p + D) ^ D) ∧
      C * U ≤ Real.exp ((p + D) ^ D) ∧ V * C ≤ Real.exp ((p + D) ^ D) := by
  let T := A + B + E + F + 5
  have hT : 2 ≤ T := by dsimp [T]; omega
  have hshift {N : ℕ} (hN : 1 ≤ N) (hNT : N ≤ T) :
      Real.exp ((p + N) ^ N) ≤ Real.exp ((p + T) ^ T) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hp hN hNT)
  have hCq := hCp.trans (hshift (by omega) (by dsimp [T]; omega))
  have hUq := hUp.trans (hshift (by omega) (by dsimp [T]; omega))
  have hVq := hVp.trans (hshift (by omega) (by dsimp [T]; omega))
  have hCU := product_two_power_bounds T hT hU hp hCq hUq
  have hVC := product_two_power_bounds T hT hC hp hVq hCq
  have hr := quotientCoordinateRadius_inverse_power_budget A B hA hB hδ hC hp d hd hδp hCp
  have hr' : 1 / quotientCoordinateRadius δ C d ≤ Real.exp ((p + (T + 5 : ℕ)) ^ (T + 5)) :=
    hr.trans (Real.exp_le_exp.mpr (shifted_power_self_mono (C := A + B + 3) (D := T + 5)
      hp (by omega) (by dsimp [T]; omega)))
  have heq : T + 5 = A + B + E + F + 10 := rfl
  simpa only [heq] using And.intro hr' (And.intro hCU hVC)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHUniformQuotientCharts
namespace OAI

section

namespace Erdos3

variable {X : Type*}

variable {ι : Type*} [Fintype ι]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open Module _root_.MvPolynomial

end Erdos3

end

section

namespace Erdos3

open Module

end Erdos3

end

section

namespace Erdos3

open Module

end Erdos3

end

section

namespace Erdos3

open Module

end Erdos3

end

section

namespace Erdos3

open Module
open scoped NNReal

namespace NilpotentLieBCHGroup

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

section Quotient

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))

end Quotient

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem quotient_coordinate_chart_metric_bounds
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l) :
    letI := rightMetricSpace (hnil := hnil) e
    ∀ C : ℝ≥0, 0 < C → ∀ z : NilpotentLieBCHGroup L s hnil,
      LipschitzWith C (fun x => z * x) → LipschitzWith C (fun x => z⁻¹ * x) →
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        4 * (C : ℝ) ^ 2 * (Fintype.card ι + 1) * r ≤ bchLatticeSeparationRadius s (Fintype.card ι) H l →
        letI := quotientMetricSpace e Γ hΓ
        ∀ v w : ι → ℝ, (∀ i, |v i| ≤ r) → (∀ i, |w i| ≤ r) →
          let q := fun u => (QuotientGroup.mk (z * (basisHomeomorph e).symm u) : _ ⧸ Γ)
          dist (q v) (q w) ≤ (C : ℝ) * (bchBoxMetricConstant s (Fintype.card ι) H 1 : ℝ) * dist v w ∧
          dist v w ≤ (bchInverseBoxConstant s (Fintype.card ι) H 1 : ℝ) * C * dist (q v) (q w) := by
  let := rightMetricSpace (hnil := hnil) e
  intro C hC z hleft hleftInv r hr hr1 hsmall
  let := quotientMetricSpace e Γ hΓ
  intro v w hv hw
  have hC' : (0 : ℝ) < C := hC
  have hR : (C : ℝ) * (Fintype.card ι + 1) * r ≤
      bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * C) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * C)).mpr
    calc
      ((C : ℝ) * (Fintype.card ι + 1) * r) * (4 * C) =
          4 * (C : ℝ) ^ 2 * (Fintype.card ι + 1) * r := by ring
      _ ≤ _ := hsmall
  have hball (u : ι → ℝ) (hu : ∀ i, |u i| ≤ r) :
      dist (z * (basisHomeomorph e).symm u) z ≤
        bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * C) := by
    have hlog : dist ((basisHomeomorph (hnil := hnil) e).symm u) 1 ≤ (Fintype.card ι + 1) * r := by
      calc
        _ = dist 1 ((basisHomeomorph (hnil := hnil) e).symm u) := dist_comm _ _
        _ ≤ coordinateL2Norm (basisHomeomorph e ((basisHomeomorph (hnil := hnil) e).symm u)) :=
          dist_one_le_coordinateL2Norm e _
        _ = coordinateL2Norm u := by rw [Homeomorph.apply_symm_apply]
        _ ≤ _ := coordinateL2Norm_le_card_bound u hr hu
    have htrans := hleft.dist_le_mul ((basisHomeomorph (hnil := hnil) e).symm u) 1
    rw [mul_one] at htrans
    calc
      _ ≤ (C : ℝ) * dist ((basisHomeomorph (hnil := hnil) e).symm u) 1 := htrans
      _ ≤ (C : ℝ) * ((Fintype.card ι + 1) * r) := mul_le_mul_of_nonneg_left hlog C.coe_nonneg
      _ = (C : ℝ) * (Fintype.card ι + 1) * r := by ring
      _ ≤ _ := hR
  have hq := quotient_dist_eq_on_ball_of_lattice_grid e c hstructure hc Γ hΓ l hl hgrid C hC z
    hleftInv (hball v hv) (hball w hw)
  have hv1 (i) : |v i| ≤ (1 : ℝ) := (hv i).trans hr1
  have hw1 (i) : |w i| ≤ (1 : ℝ) := (hw i).trans hr1
  have hforward := (lipschitzOn_basisHomeomorph_symm_box (hnil := hnil) e c hstructure hc 1 le_rfl).dist_le_mul v hv1 w hw1
  have hinverse := dist_coordinates_le_bchInverseBoxConstant e c hstructure hc 1 le_rfl
    ((basisHomeomorph (hnil := hnil) e).symm v) ((basisHomeomorph (hnil := hnil) e).symm w)
    (fun i => by
      change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm v) i| ≤ _
      simpa only [Homeomorph.apply_symm_apply, NNReal.coe_one] using hv1 i)
    (fun i => by
      change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm w) i| ≤ _
      simpa only [Homeomorph.apply_symm_apply, NNReal.coe_one] using hw1 i)
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply] at hinverse
  dsimp only
  rw [hq]
  constructor
  · apply (hleft.dist_le_mul _ _).trans
    exact (mul_le_mul_of_nonneg_left hforward C.coe_nonneg).trans_eq (by ring)
  · have hback : dist ((basisHomeomorph (hnil := hnil) e).symm v) ((basisHomeomorph (hnil := hnil) e).symm w) ≤
        (C : ℝ) * dist (z * (basisHomeomorph e).symm v) (z * (basisHomeomorph e).symm w) := by
      have hb := hleftInv.dist_le_mul
        (z * (basisHomeomorph e).symm v) (z * (basisHomeomorph e).symm w)
      rw [inv_mul_cancel_left, inv_mul_cancel_left] at hb
      exact hb
    exact hinverse.trans ((mul_le_mul_of_nonneg_left hback (bchInverseBoxConstant _ _ _ _).coe_nonneg).trans_eq (by ring))

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

theorem exists_uniform_quotient_chart_metric_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
      [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
      (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) (l : ℕ),
      0 < l → (∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l) →
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      letI := quotientMetricSpace e Γ hΓ
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 1 / r ≤ Real.exp ((p + D) ^ D) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
          ∀ z : NilpotentLieBCHGroup L s hnil,
            (∀ i, |e.repr z.coord i| ≤ Real.exp ((p + 2) ^ a)) →
            ∀ v w : ι → ℝ, (∀ i, |v i| ≤ r) → (∀ i, |w i| ≤ r) →
              let q := fun u => (QuotientGroup.mk (z * (basisHomeomorph e).symm u) : _ ⧸ Γ)
              dist (q v) (q w) ≤ K * dist v w ∧ dist v w ≤ K * dist (q v) (q w) := by
  obtain ⟨A, hA, hgap⟩ := exists_bchLatticeSeparationRadius_inv_exp_bound s
  obtain ⟨B, hB, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s a
  obtain ⟨E, hE, hforward⟩ := exists_bchBoxMetricConstant_exp_bound s 0
  obtain ⟨F, hF, hinverse⟩ := exists_bchInverseBoxConstant_exp_bound s 0
  refine ⟨A + B + E + F + 10, by omega, ?_⟩
  intro ι L _ _ _ _ _ _ _ _ _ e c H p hnil Γ hΓ l hl hgrid hstructure hc hp hd hH hlp
  let := rightMetricSpace (hnil := hnil) e
  let := quotientMetricSpace e Γ hΓ
  obtain ⟨C, hC, hCp, hleft⟩ := hleft e c H p hnil hstructure hp hd hH hc
  let δ := bchLatticeSeparationRadius s (Fintype.card ι) H l
  have hδ : 0 < δ := bchLatticeSeparationRadius_pos _ _ _ _
  let r := quotientCoordinateRadius δ (C : ℝ) (Fintype.card ι)
  let U := bchBoxMetricConstant s (Fintype.card ι) H 1
  let V := bchInverseBoxConstant s (Fintype.card ι) H 1
  have hunit : ((1 : ℝ≥0) : ℝ) ≤ Real.exp ((p + 2) ^ 0) := by
    simpa only [NNReal.coe_one, pow_zero] using Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨hrp, hCU, hVC⟩ := quotient_chart_parameter_budget A B E F hA hB hE hF
    hδ C.coe_nonneg U.coe_nonneg hp (Fintype.card ι) hd
    (hgap _ _ _ _ hp hd hH hlp) hCp
    (hforward _ _ 1 _ hp hd hH hunit) (hinverse _ _ 1 _ hp hd hH hunit)
  let K : ℝ≥0 := max (C * U) (V * C)
  have hK : (K : ℝ) ≤ Real.exp ((p + (A + B + E + F + 10 : ℕ)) ^ (A + B + E + F + 10)) := by
    simpa only [K, NNReal.coe_max, NNReal.coe_mul] using max_le hCU hVC
  have hKU : (C : ℝ) * U ≤ (K : ℝ) := by exact_mod_cast (le_max_left (C * U) (V * C))
  have hKV : (V : ℝ) * C ≤ (K : ℝ) := by exact_mod_cast (le_max_right (C * U) (V * C))
  refine ⟨r, quotientCoordinateRadius_pos hδ _, quotientCoordinateRadius_le_one hδ _, hrp, K, hK, ?_⟩
  intro z hz v w hv hw
  have hzinv (i) : |e.repr z⁻¹.coord i| ≤ Real.exp ((p + 2) ^ a) := by
    simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hz i
  obtain ⟨hvw, hwv⟩ := quotient_coordinate_chart_metric_bounds e c hstructure hc Γ hΓ l hl hgrid
    C hC z (hleft z hz) (hleft z⁻¹ hzinv) r (quotientCoordinateRadius_pos hδ _).le
    (quotientCoordinateRadius_le_one hδ _) (quotientCoordinateRadius_small hδ _) v w hv hw
  exact ⟨hvw.trans (mul_le_mul_of_nonneg_right hKU dist_nonneg),
    hwv.trans (mul_le_mul_of_nonneg_right hKV dist_nonneg)⟩

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealifiedBCHFiniteAtlas
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
  (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)

theorem quotientCoordinateChart_apply (z : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    quotientCoordinateChart e c hstructure hc Γ l hl hgrid z v =
      (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ) := rfl

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

namespace NilpotentLieBCHGroup

theorem quotient_covered_by_coordinate_box {ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
    [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
    {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℝ)
    (hrep : ∀ g : NilpotentLieBCHGroup L s hnil, ∃ z,
      (∀ i, |e.repr z.coord i| ≤ B) ∧ ∃ γ ∈ Γ, g = z * γ) :
    ∀ x : NilpotentLieBCHGroup L s hnil ⧸ Γ, ∃ v : ι → ℝ,
      (∀ i, |v i| ≤ B) ∧ (QuotientGroup.mk ((basisHomeomorph e).symm v) : _ ⧸ Γ) = x := by
  intro x
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨z, hz, γ, hγ, hg⟩ := hrep g
    refine ⟨basisHomeomorph e z, hz, ?_⟩
    rw [Homeomorph.symm_apply_apply, hg]
    exact (quotient_mk_mul_mem Γ z ⟨γ, hγ⟩).symm

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set Manifold
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
  (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)

theorem quotientChartedSpace_chartAt (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    letI := quotientChartedSpace e c hstructure hc Γ l hl hgrid
    chartAt (ι → ℝ) x = (quotientCoordinateChart e c hstructure hc Γ l hl hgrid x.out).symm := rfl

theorem quotientCoordinateChart_mem_atlas (z : NilpotentLieBCHGroup L s hnil) :
    letI := quotientChartedSpace e c hstructure hc Γ l hl hgrid
    (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z).symm ∈
      atlas (ι → ℝ) (NilpotentLieBCHGroup L s hnil ⧸ Γ) := ⟨z, rfl⟩

theorem isManifold_quotient (n : ℕ∞ω) :
    letI := quotientChartedSpace e c hstructure hc Γ l hl hgrid
    IsManifold 𝓘(ℝ, ι → ℝ) n (NilpotentLieBCHGroup L s hnil ⧸ Γ) := by
  let := quotientChartedSpace e c hstructure hc Γ l hl hgrid
  apply isManifold_of_contDiffOn
  intro φ ψ hφ hψ
  obtain ⟨z, rfl⟩ := hφ
  obtain ⟨w, rfl⟩ := hψ
  simpa only [OpenPartialHomeomorph.symm_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    preimage_id, range_id, inter_univ] using
    contDiffOn_quotient_chart_transition e Γ z w
      (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z)
      (quotientCoordinateChart e c hstructure hc Γ l hl hgrid w)
      (quotientCoordinateChart_apply e c hstructure hc Γ l hl hgrid z)
      (quotientCoordinateChart_apply e c hstructure hc Γ l hl hgrid w) n

theorem contMDiff_quotient_mk (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := quotientChartedSpace e c hstructure hc Γ l hl hgrid
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n
      (QuotientGroup.mk : NilpotentLieBCHGroup L s hnil → _ ⧸ Γ) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := basisChartedSpace (hnil := hnil) e
  let := quotientChartedSpace e c hstructure hc Γ l hl hgrid
  intro g
  apply contMDiffAt_iff_target.mpr
  refine ⟨QuotientGroup.continuous_mk.continuousAt, ?_⟩
  have h := contMDiffAt_quotient_chartInverse e Γ (QuotientGroup.mk g : _ ⧸ Γ).out
    (quotientCoordinateChart e c hstructure hc Γ l hl hgrid (QuotientGroup.mk g : _ ⧸ Γ).out)
    (quotientCoordinateChart_apply e c hstructure hc Γ l hl hgrid _) n g
    (by simpa only [QuotientGroup.out_eq'] using
      quotientCoordinateChart_center_mem e c hstructure hc Γ l hl hgrid (QuotientGroup.mk g : _ ⧸ Γ).out)
  simpa only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.coe_toPartialEquiv,
    modelWithCornersSelf_coe, Function.id_comp, quotientChartedSpace_chartAt,
    Function.comp_def, Function.id_def] using h

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem inv_mul_coordinates_bound
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (u v : NilpotentLieBCHGroup L s hnil) {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hu : ∀ i, |e.repr u.coord i| ≤ B) (hv : ∀ i, |e.repr v.coord i| ≤ B)
    (huv : ∀ i, |e.repr u.coord i - e.repr v.coord i| ≤ δ) (k : ι) :
    |e.repr (u⁻¹ * v).coord k| ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * δ := by
  simpa only [coord_mul, coord_inv, neg_neg] using
    lieBCH_sub_coordinates_bound e c hstructure hc hnil (-u.coord) (-v.coord) hB hδ
      (fun i => by simpa only [map_neg, Finsupp.neg_apply, abs_neg] using hu i)
      (fun i => by simpa only [map_neg, Finsupp.neg_apply, abs_neg] using hv i)
      (fun i => by simpa only [map_neg, Finsupp.neg_apply, neg_sub_neg, abs_sub_comm] using huv i) k

variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

theorem finite_quotient_coordinate_cover
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (B : ℝ) (hB : 1 ≤ B)
    (hrep : ∀ g : NilpotentLieBCHGroup L s hnil, ∃ z,
      (∀ i, |e.repr z.coord i| ≤ B) ∧ ∃ γ ∈ Γ, g = z * γ)
    (r : ℝ) (hr : 0 < r) :
    let K : ℝ≥0 := ⟨bchBoxCoordinateBound s (Fintype.card ι) H B,
      bchBoxCoordinateBound_nonneg _ _ _ (by linarith)⟩
    let n := (boxCoverMeshCount B K (r / 2) + 1) ^ Fintype.card ι
    ∃ centers : Fin n → NilpotentLieBCHGroup L s hnil,
      (∀ j i, |e.repr (centers j).coord i| ≤ B) ∧
      ∀ x : NilpotentLieBCHGroup L s hnil ⧸ Γ, ∃ j, ∃ u : ι → ℝ,
        (∀ i, |u i| ≤ r / 2) ∧
        (QuotientGroup.mk (centers j * (basisHomeomorph e).symm u) : _ ⧸ Γ) = x := by
  classical
  let K : ℝ≥0 := ⟨bchBoxCoordinateBound s (Fintype.card ι) H B,
    bchBoxCoordinateBound_nonneg _ _ _ (by linarith)⟩
  let N := boxCoverMeshCount B K (r / 2)
  let n := (N + 1) ^ Fintype.card ι
  let I := ι → Fin (N + 1)
  have hN : 0 < N := boxCoverMeshCount_pos _ _ _
  have hcard : Fintype.card I = n := by simp [I, n]
  let reindex : I ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let centers : Fin n → NilpotentLieBCHGroup L s hnil := fun j =>
    (basisHomeomorph e).symm (uniformBoxGrid B N (reindex.symm j))
  have hcenters (j : Fin n) : e.equivFun (centers j).coord = uniformBoxGrid B N (reindex.symm j) :=
    (basisHomeomorph (hnil := hnil) e).apply_symm_apply _
  have hcentersB (j i) : |e.repr (centers j).coord i| ≤ B := by
    have := uniformBoxGrid_mem (ι := ι) (by linarith : 0 ≤ B) hN (reindex.symm j) i
    simpa only [← hcenters j, Basis.equivFun_apply] using this
  refine ⟨centers, hcentersB, ?_⟩
  intro x
  obtain ⟨v, hv, hvx⟩ := quotient_covered_by_coordinate_box e Γ B hrep x
  obtain ⟨k, hk⟩ := exists_uniformBoxGrid_approx (by linarith : 0 < B) hN v hv
  let j := reindex k
  let g := (basisHomeomorph (hnil := hnil) e).symm v
  have hgv : e.equivFun g.coord = v := (basisHomeomorph (hnil := hnil) e).apply_symm_apply v
  have hgB (i) : |e.repr g.coord i| ≤ B := by
    simpa only [← hgv, Basis.equivFun_apply] using hv i
  have hdiff (i) : |e.repr (centers j).coord i - e.repr g.coord i| ≤ 2 * B / N := by
    have hi := (dist_pi_le_iff (by positivity : 0 ≤ 2 * B / (N : ℝ))).mp hk i
    have hj : reindex.symm j = k := reindex.symm_apply_apply k
    have hci : e.repr (centers j).coord i = uniformBoxGrid B N k i := by
      simpa only [Basis.equivFun_apply, hj] using congrFun (hcenters j) i
    have hgi : e.repr g.coord i = v i := by
      simpa only [Basis.equivFun_apply] using congrFun hgv i
    simpa only [Real.dist_eq, ← hci, ← hgi, abs_sub_comm] using hi
  have herror : (K : ℝ) * (2 * B / N) ≤ r / 2 := boxCoverMeshCount_error K (by linarith)
  have hsmall (i) : |e.repr ((centers j)⁻¹ * g).coord i| ≤ r / 2 :=
    (inv_mul_coordinates_bound e c hstructure hc (centers j) g hB
      (by positivity) (hcentersB j) hgB hdiff i).trans herror
  refine ⟨j, basisHomeomorph e ((centers j)⁻¹ * g), hsmall, ?_⟩
  simp only [Homeomorph.symm_apply_apply, mul_inv_cancel_left]
  exact hvx

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set Manifold
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem quotient_chart_transition_mem_contDiffGroupoid
    (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (z w : NilpotentLieBCHGroup L s hnil) (φ ψ : OpenPartialHomeomorph (ι → ℝ) (_ ⧸ Γ))
    (hφ : ∀ v, φ v = QuotientGroup.mk (z * (basisHomeomorph e).symm v))
    (hψ : ∀ v, ψ v = QuotientGroup.mk (w * (basisHomeomorph e).symm v)) (n : ℕ∞ω) :
    φ.trans ψ.symm ∈ contDiffGroupoid n 𝓘(ℝ, ι → ℝ) := by
  simp only [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    preimage_id, range_id, inter_univ]
  constructor
  · exact contDiffOn_quotient_chart_transition e Γ z w φ ψ hφ hψ n
  · exact contDiffOn_quotient_chart_transition e Γ w z ψ φ hψ hφ n

theorem quotient_chart_mem_maximalAtlas
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)
    (z : NilpotentLieBCHGroup L s hnil) (φ : OpenPartialHomeomorph (ι → ℝ) (_ ⧸ Γ))
    (hφ : ∀ v, φ v = QuotientGroup.mk (z * (basisHomeomorph e).symm v)) (n : ℕ∞ω) :
    letI := quotientChartedSpace e c hstructure hc Γ l hl hgrid
    φ.symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, ι → ℝ) n (NilpotentLieBCHGroup L s hnil ⧸ Γ) := by
  let := quotientChartedSpace e c hstructure hc Γ l hl hgrid
  intro ψ hψ
  obtain ⟨w, rfl⟩ := hψ
  constructor
  · simpa only [OpenPartialHomeomorph.symm_symm] using
      quotient_chart_transition_mem_contDiffGroupoid e Γ z w φ
        (quotientCoordinateChart e c hstructure hc Γ l hl hgrid w) hφ
        (quotientCoordinateChart_apply e c hstructure hc Γ l hl hgrid w) n
  · simpa only [OpenPartialHomeomorph.symm_symm] using
      quotient_chart_transition_mem_contDiffGroupoid e Γ w z
        (quotientCoordinateChart e c hstructure hc Γ l hl hgrid w) φ
        (quotientCoordinateChart_apply e c hstructure hc Γ l hl hgrid w) hφ n

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem half_radius_inverse_power_bound (C : ℕ) (hC : 2 ≤ C) {r p : ℝ}
    (hr : 0 < r) (hp : 0 ≤ p) (hri : 1 / r ≤ Real.exp ((p + C) ^ C)) :
    1 / (r / 2) ≤ Real.exp ((p + (C + 3 : ℕ)) ^ (C + 3)) := by
  have h := metricPartition_constant_power_budget C 1 hC ⟨r, hr.le⟩ hp
    (by simpa only [Nat.cast_one] using Real.one_le_exp (by positivity : 0 ≤ (p + C) ^ C)) hri
  have hthree : 3 / r ≤ Real.exp ((p + (C + 3 : ℕ)) ^ (C + 3)) := by
    norm_num at h ⊢
    exact h
  apply le_trans ?_ hthree
  rw [show 1 / (r / 2) = 2 / r by ring]
  exact div_le_div_of_nonneg_right (by norm_num) hr.le

theorem exists_bch_flexible_cover_exp_bound (s C₀ Cᵣ : ℕ) (hC₀ : 2 ≤ C₀) (hCᵣ : 2 ≤ Cᵣ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ (d H : ℕ) (p r : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      0 < r → 1 / r ≤ Real.exp ((p + Cᵣ) ^ Cᵣ) →
      let B := Real.exp ((p + C₀) ^ C₀)
      let K : ℝ≥0 := ⟨bchBoxCoordinateBound s d H B,
        bchBoxCoordinateBound_nonneg _ _ _ (Real.exp_nonneg _)⟩
      (((boxCoverMeshCount B K (r / 2) + 1) ^ d : ℕ) : ℝ) ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C₁, hC₁, hinput⟩ := exists_bch_partition_input_exp_bound s 0 C₀ hC₀
  let C := C₁ + Cᵣ + 5
  have hC : 2 ≤ C := by dsimp [C]; omega
  refine ⟨C + 5, by omega, ?_⟩
  intro d H p r hp hd hH hr hri
  let B := Real.exp ((p + C₀) ^ C₀)
  let K : ℝ≥0 := ⟨bchBoxCoordinateBound s d H B,
    bchBoxCoordinateBound_nonneg _ _ _ (Real.exp_nonneg _)⟩
  obtain ⟨hB, hmetric, _⟩ := hinput d H p hp hd hH
  have hshift := Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := C₁) (D := C) hp (by omega) (by dsimp [C]; omega))
  have hBC := hB.trans hshift
  have hKC : (K : ℝ) ≤ Real.exp ((p + C) ^ C) :=
    (bchBoxCoordinateBound_le_bchBoxMetricConstant s d H ⟨B, Real.exp_nonneg _⟩).trans
      (hmetric.trans hshift)
  have hhalf := (half_radius_inverse_power_bound Cᵣ hCᵣ hr hp hri).trans
    (Real.exp_le_exp.mpr (shifted_power_self_mono (C := Cᵣ + 3) (D := C)
      hp (by omega) (by dsimp [C]; omega)))
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    boxCoverCount_le_exp C d hC K (Real.exp_nonneg _) (by linarith) hp hd hBC hKC hhalf

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
namespace OAI

section

namespace Erdos3

open Module

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set Manifold
open scoped Manifold ContDiff Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
  (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)

theorem contMDiff_of_quotient_pullback
    {E' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace N] [ChartedSpace E' N] (n : ℕ∞ω)
    (F : (NilpotentLieBCHGroup L s hnil ⧸ Γ) → N) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := quotientChartedSpace e c hstructure hc Γ l hl hgrid
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, E') n
      (fun g : NilpotentLieBCHGroup L s hnil => F (QuotientGroup.mk g)) →
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, E') n F := by
  let := basisChartedSpace (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e n
  let := quotientChartedSpace e c hstructure hc Γ l hl hgrid
  let := isManifold_quotient e c hstructure hc Γ l hl hgrid n
  intro hF x
  let z := x.out
  let φ := quotientCoordinateChart e c hstructure hc Γ l hl hgrid z
  have hx : x ∈ φ.target := by
    simpa only [z, QuotientGroup.out_eq'] using quotientCoordinateChart_center_mem e c hstructure hc Γ l hl hgrid z
  have hφ : φ.symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, ι → ℝ) n (_ ⧸ Γ) :=
    IsManifold.subset_maximalAtlas (quotientCoordinateChart_mem_atlas e c hstructure hc Γ l hl hgrid z)
  have hchart : ContMDiffAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n φ.symm x :=
    contMDiffAt_of_mem_maximalAtlas hφ hx
  let σ := fun y : NilpotentLieBCHGroup L s hnil ⧸ Γ => z * (basisHomeomorph e).symm (φ.symm y)
  have hσ : ContMDiffAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n σ x :=
    contMDiffAt_const.mul ((contMDiff_basisHomeomorph_symm e n).contMDiffAt.comp x hchart)
  apply (hF.contMDiffAt.comp x hσ).congr_of_eventuallyEq
  filter_upwards [φ.open_target.mem_nhds hx] with y hy
  have hq : (QuotientGroup.mk (σ y) : _ ⧸ Γ) = y :=
    (quotientCoordinateChart_apply e c hstructure hc Γ l hl hgrid z (φ.symm y)).symm.trans (φ.right_inv hy)
  change F y = F (QuotientGroup.mk (σ y))
  rw [hq]

theorem contMDiff_quotient_iff
    {E' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace N] [ChartedSpace E' N] (n : ℕ∞ω)
    (F : (NilpotentLieBCHGroup L s hnil ⧸ Γ) → N) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := quotientChartedSpace e c hstructure hc Γ l hl hgrid
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, E') n F ↔
      ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, E') n
        (fun g : NilpotentLieBCHGroup L s hnil => F (QuotientGroup.mk g)) := by
  let := basisChartedSpace (hnil := hnil) e
  let := quotientChartedSpace e c hstructure hc Γ l hl hgrid
  constructor
  · intro hF
    exact hF.comp (contMDiff_quotient_mk e c hstructure hc Γ l hl hgrid n)
  · exact contMDiff_of_quotient_pullback e c hstructure hc Γ l hl hgrid n F

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

local notation "G" => NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)

variable (e : Basis ι ℚ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (l : ℕ) (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)

theorem contMDiff_realification_quotient_iff
    {E' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace N] [ChartedSpace E' N] (n : ℕ∞ω)
    (F : (G ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) → N) :
    letI := NilpotentLieBCHGroup.basisChartedSpace
      (hnil := realification_lowerCentralSeries_eq_bot hnil) (e.baseChange ℝ)
    letI := realificationQuotientChartedSpace e Γ l hl houter hc
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, E') n F ↔
      ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, E') n (fun g : G => F (QuotientGroup.mk g)) :=
  NilpotentLieBCHGroup.contMDiff_quotient_iff (e.baseChange ℝ) (lieStructureConstants e)
    (fun i j k => (realLieBasis_structure e i j k).symm) hc
    (Γ.map NilpotentLieBCHGroup.realificationHom) l hl
    (NilpotentLieBCHGroup.realification_subgroup_grid e Γ l houter) n F

theorem realification_quotient_chart_mem_maximalAtlas
    (z : G) (φ : OpenPartialHomeomorph (ι → ℝ) (G ⧸ Γ.map NilpotentLieBCHGroup.realificationHom))
    (hφ : ∀ v, φ v = QuotientGroup.mk (z * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm v))
    (n : ℕ∞ω) :
    letI := realificationQuotientChartedSpace e Γ l hl houter hc
    φ.symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, ι → ℝ) n (G ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) :=
  NilpotentLieBCHGroup.quotient_chart_mem_maximalAtlas (e.baseChange ℝ) (lieStructureConstants e)
    (fun i j k => (realLieBasis_structure e i j k).symm) hc
    (Γ.map NilpotentLieBCHGroup.realificationHom) l hl
    (NilpotentLieBCHGroup.realification_subgroup_grid e Γ l houter) z φ hφ n

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct Manifold ContDiff

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s H₁ H₂ : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct Manifold ContDiff

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

namespace RationalFilteredNilmanifold

variable {L} {s d : ℕ} (D : RationalFilteredNilmanifold L s d)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d) (hD : D.filtration.layer (s + 1) = ⊥)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

namespace Niltest

variable {D} {w : σ → ℕ}

end Niltest
end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)

end Erdos3.RationalFilteredNilmanifold

end

section

open Module
open scoped BigOperators

namespace Erdos3

namespace NilpotentLieFiltration

variable {ι : Type*} {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealifiedBCHSmoothPartition
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

theorem exists_realification_quotient_chart_metric_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ)
      (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l),
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      letI := realificationQuotientMetricSpace e Γ l hl houter
      let G := NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)
      let ΓR : Subgroup G := Γ.map NilpotentLieBCHGroup.realificationHom
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 1 / r ≤ Real.exp ((p + D) ^ D) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
          ∀ z : G,
            (∀ i, |(e.baseChange ℝ).repr z.coord i| ≤ Real.exp ((p + 2) ^ a)) →
            ∀ v w : ι → ℝ, (∀ i, |v i| ≤ r) → (∀ i, |w i| ≤ r) →
              let q := fun u => (QuotientGroup.mk
                (z * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm u) : G ⧸ ΓR)
              dist (q v) (q w) ≤ K * dist v w ∧ dist v w ≤ K * dist (q v) (q w) := by
  obtain ⟨D, hD, hchart⟩ := NilpotentLieBCHGroup.exists_uniform_quotient_chart_metric_exp_bound s a
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ _ _ e hnil Γ l H p hl houter hc hp hd hH hlp
  exact hchart (e.baseChange ℝ) (lieStructureConstants e) H p
    (realification_lowerCentralSeries_eq_bot hnil) (Γ.map NilpotentLieBCHGroup.realificationHom)
    (NilpotentLieBCHGroup.realification_subgroup_closed_discrete e Γ l hl houter).1 l hl
    (NilpotentLieBCHGroup.realification_subgroup_grid e Γ l houter)
    (fun i j k => (realLieBasis_structure e i j k).symm) hc hp hd hH hlp

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

theorem exists_realification_bilipschitz_charts_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ)
      (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l),
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      letI := realificationQuotientMetricSpace e Γ l hl houter
      let G := NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)
      let ΓR : Subgroup G := Γ.map NilpotentLieBCHGroup.realificationHom
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 1 / r ≤ Real.exp ((p + D) ^ D) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
          ∀ z : G, (∀ i, |(e.baseChange ℝ).repr z.coord i| ≤ Real.exp ((p + 2) ^ a)) →
            ∃ φ : OpenPartialHomeomorph (ι → ℝ) (G ⧸ ΓR),
              (∀ v, φ v = (QuotientGroup.mk
                (z * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm v) : G ⧸ ΓR)) ∧
              φ.source = {v | ∀ i, |v i| < r} ∧
              LipschitzOnWith K φ φ.source ∧ LipschitzOnWith K φ.symm φ.target := by
  obtain ⟨D, hD, hmetric⟩ := exists_realification_quotient_chart_metric_exp_bound s a
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ _ _ e hnil Γ l H p hl houter hc hp hd hH hlp
  let := realificationQuotientMetricSpace e Γ l hl houter
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (e.baseChange ℝ).finiteDimensional_of_finite
  obtain ⟨r, hr, hr1, hrp, K, hK, hcharts⟩ := hmetric e hnil Γ l H p hl houter hc hp hd hH hlp
  refine ⟨r, hr, hr1, hrp, K, hK, ?_⟩
  intro z hz
  let q := fun v : ι → ℝ => (QuotientGroup.mk
    (z * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm v) :
      _ ⧸ Γ.map NilpotentLieBCHGroup.realificationHom)
  have hq : Continuous q := QuotientGroup.continuous_mk.comp
    (continuous_const.mul (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm.continuous)
  have hqo : IsOpenMap q := QuotientGroup.isOpenMap_coe.comp
    ((Homeomorph.mulLeft z).isOpenMap.comp (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm.isOpenMap)
  have hU : IsOpen {v : ι → ℝ | ∀ i, |v i| < r} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt (continuous_apply i).abs continuous_const)
  obtain ⟨φ, hφ, hsource, _, hLip, hInv⟩ := exists_openPartialHomeomorph_of_metric_bounds q hq hqo
    {v : ι → ℝ | ∀ i, |v i| < r} hU K
    (fun v hv w hw => (hcharts z hz v w (fun i => (hv i).le) (fun i => (hw i).le)).1)
    (fun v hv w hw => (hcharts z hz v w (fun i => (hv i).le) (fun i => (hw i).le)).2)
  exact ⟨φ, hφ, hsource, hLip, hInv⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

theorem exists_realification_finite_bilipschitz_atlas_exp_bound (s : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ)
      (hl : 0 < l) (_hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
      (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l),
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      letI := realificationQuotientMetricSpace e Γ l hl houter
      let G := NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)
      let ΓR : Subgroup G := Γ.map NilpotentLieBCHGroup.realificationHom
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 1 / r ≤ Real.exp ((p + D) ^ D) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∃ centers : Fin n → G, ∃ φ : Fin n → OpenPartialHomeomorph (ι → ℝ) (G ⧸ ΓR),
          (∀ j i, |(e.baseChange ℝ).repr (centers j).coord i| ≤ Real.exp ((p + D) ^ D)) ∧
          (∀ j v, φ j v = (QuotientGroup.mk
            (centers j * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm v) : G ⧸ ΓR)) ∧
          (∀ j, (φ j).source = {v | ∀ i, |v i| < r}) ∧
          (∀ j, LipschitzOnWith K (φ j) (φ j).source) ∧
          (∀ j, LipschitzOnWith K (φ j).symm (φ j).target) ∧
          (∀ x : G ⧸ ΓR, ∃ j, ∃ u : ι → ℝ, (∀ i, |u i| ≤ r / 2) ∧ φ j u = x) := by
  obtain ⟨C₀, hC₀, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨C₁, hC₁, hcharts⟩ := exists_realification_bilipschitz_charts_exp_bound s C₀
  let Cᵣ := C₀ + C₁ + 2
  have hCᵣ : 2 ≤ Cᵣ := by dsimp [Cᵣ]; omega
  obtain ⟨C₂, hC₂, hcount⟩ := exists_bch_flexible_cover_exp_bound s C₀ Cᵣ hC₀ hCᵣ
  let D := Cᵣ + C₂ + 2
  have hD : 2 ≤ D := by dsimp [D]; omega
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ _ _ e hnil Γ l H p hl hinner houter hc hp hd hH hlp
  let := realificationQuotientMetricSpace e Γ l hl houter
  have hpq : 0 ≤ p + C₀ := by positivity
  have hdq : (Fintype.card ι : ℝ) ≤ p + C₀ := hd.trans (by linarith [Nat.cast_nonneg (α := ℝ) C₀])
  have hep : Real.exp p ≤ Real.exp (p + C₀) := Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) C₀])
  obtain ⟨r, hr, hr1, hrp, K, hKp, hcharts⟩ :=
    hcharts e hnil Γ l H (p + C₀) hl houter hc hpq hdq (hH.trans hep) (hlp.trans hep)
  have hshift : Real.exp (((p + C₀) + C₁) ^ C₁) ≤ Real.exp ((p + Cᵣ) ^ Cᵣ) :=
    Real.exp_le_exp.mpr (shifted_center_power_bound C₀ C₁ hp)
  have hrC := hrp.trans hshift
  have hKC := hKp.trans hshift
  have hRD := Real.exp_le_exp.mpr (shifted_power_self_mono (C := Cᵣ) (D := D)
    hp (by omega) (by dsimp [D]; omega))
  let B := Real.exp ((p + C₀) ^ C₀)
  have hB : 1 ≤ B := Real.one_le_exp (by positivity)
  have hBD : B ≤ Real.exp ((p + D) ^ D) := Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := C₀) (D := D) hp (by omega) (by dsimp [D, Cᵣ]; omega))
  have hBZ : B ≤ Real.exp (((p + C₀) + 2) ^ C₀) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) C₀)
  obtain ⟨centers, hcenters, hcover⟩ := NilpotentLieBCHGroup.finite_quotient_coordinate_cover
    (e.baseChange ℝ) (lieStructureConstants e) (fun i j k => (realLieBasis_structure e i j k).symm) hc
    (Γ.map NilpotentLieBCHGroup.realificationHom) B hB
    (hrep e hnil Γ l H p hl hinner hc hp hd hH hlp) r hr
  choose φ hφ hsource hLip hInv using fun j => hcharts (centers j) (fun i => (hcenters j i).trans hBZ)
  have hn := (hcount (Fintype.card ι) H p r hp hd hH hr hrC).trans
    (Real.exp_le_exp.mpr (shifted_power_self_mono (C := C₂) (D := D)
      hp (by omega) (by dsimp [D]; omega)))
  refine ⟨r, hr, hr1, hrC.trans hRD, K, hKC.trans hRD, _, by positivity, hn,
    centers, φ, fun j i => (hcenters j i).trans hBD, hφ, hsource, hLip, hInv, ?_⟩
  intro x
  obtain ⟨j, u, hu, heq⟩ := hcover x
  exact ⟨j, u, hu, (hφ j u).trans heq⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal Manifold ContDiff

theorem exists_realification_smooth_partition_exp_bound (s : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ)
      (hl : 0 < l) (_hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
      (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
      (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      letI := realificationQuotientMetricSpace e Γ l hl houter
      letI := realificationQuotientChartedSpace e Γ l hl houter hc
      let G := NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)
      let ΓR : Subgroup G := Γ.map NilpotentLieBCHGroup.realificationHom
      ∃ r : ℝ≥0, 0 < r ∧ r ≤ 1 ∧ 1 / (r : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∃ centers : Fin n → G, ∃ φ : Fin n → OpenPartialHomeomorph (ι → ℝ) (G ⧸ ΓR),
          (∀ j i, |(e.baseChange ℝ).repr (centers j).coord i| ≤ Real.exp ((p + D) ^ D)) ∧
          (∀ j v, φ j v = (QuotientGroup.mk
            (centers j * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm v) : G ⧸ ΓR)) ∧
          (∀ j, (φ j).source = {v | ∀ i, |v i| < (r : ℝ)}) ∧
          (∀ j, (φ j).symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, ι → ℝ) ∞ (G ⧸ ΓR)) ∧
          ∃ P : ℝ≥0, (P : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
          ∃ f : Fin n → (G ⧸ ΓR) → ℝ,
            (∀ j x, 0 ≤ f j x ∧ f j x ≤ 1) ∧ (∀ x, ∑ j, f j x = 1) ∧
            (∀ j, HasCompactSupport (f j) ∧ tsupport (f j) ⊆ (φ j).target) ∧
            (∀ j, ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ℝ) ∞ (f j)) ∧
            (∀ j, LipschitzWith P (f j)) ∧
            (∀ j, tsupport (f j) ⊆ φ j '' Metric.closedBall 0 (3 * (r : ℝ) / 4)) ∧
            ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
              ∀ j, LipschitzOnWith K (φ j) (φ j).source := by
  obtain ⟨D₀, hD₀, hatlas⟩ := exists_realification_finite_bilipschitz_atlas_exp_bound s
  obtain ⟨D₁, hD₁, hleft⟩ := NilpotentLieBCHGroup.exists_uniform_left_lipschitz_exp_bound s D₀
  obtain ⟨D₂, hD₂, hinverse⟩ := exists_bchInverseBoxConstant_exp_bound s 0
  obtain ⟨A, _, hcutoff⟩ := exists_smooth_box_cutoffs
  obtain ⟨N, hN⟩ := exists_nat_ge (A : ℝ)
  let T := D₀ + D₁ + D₂ + N + 5
  let D := T + 21
  have hT : 2 ≤ T := by dsimp [T]; omega
  have hD : 2 ≤ D := by dsimp [D]; omega
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ _ _ e hnil Γ l H p hl hinner houter hc hp hd hH hlp
  let := realificationQuotientMetricSpace e Γ l hl houter
  let := realificationQuotientChartedSpace e Γ l hl houter hc
  let := NilpotentLieBCHGroup.basisChartedSpace
    (hnil := realification_lowerCentralSeries_eq_bot hnil) (e.baseChange ℝ)
  let := NilpotentLieBCHGroup.rightMetricSpace
    (hnil := realification_lowerCentralSeries_eq_bot hnil) (e.baseChange ℝ)
  obtain ⟨r, hr, hr1, hri, K, hK, n, hn, hnb, centers, φ,
    hcenters, hφ, hsource, hForward, hInv, hcover⟩ :=
    hatlas e hnil Γ l H p hl hinner houter hc hp hd hH hlp
  let rN : ℝ≥0 := ⟨r, hr.le⟩
  have hstructure := fun i j k => (realLieBasis_structure e i j k).symm
  have hpq : 0 ≤ p + D₀ := by positivity
  have hdq : (Fintype.card ι : ℝ) ≤ p + D₀ := hd.trans (by linarith [Nat.cast_nonneg (α := ℝ) D₀])
  have hHq : (H : ℝ) ≤ Real.exp (p + D₀) :=
    hH.trans (Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) D₀]))
  obtain ⟨C, hC, hCb, hleft⟩ := hleft (e.baseChange ℝ) (lieStructureConstants e) H (p + D₀)
    (realification_lowerCentralSeries_eq_bot hnil) hstructure hpq hdq hHq hc
  have hcenterInv (j) : LipschitzWith C (fun x => (centers j)⁻¹ * x) := by
    apply hleft
    intro i
    have hi := (hcenters j i).trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by positivity) (show p + D₀ ≤ (p + D₀) + 2 by linarith) D₀))
    simpa only [NilpotentLieBCHGroup.coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hi
  have hclosed := (NilpotentLieBCHGroup.realification_subgroup_closed_discrete e Γ l hl houter).1
  obtain ⟨ψ, hsmooth, _, hrange, hone, hzero, hLip⟩ := hcutoff (ι := ι) rN hr
  obtain ⟨f, hfrange, hfsum, hfsupport, hfsmooth, hfLip, hfInner⟩ :=
    NilpotentLieBCHGroup.exists_smooth_quotient_chart_partition (e.baseChange ℝ) (lieStructureConstants e)
      hstructure hc (Γ.map NilpotentLieBCHGroup.realificationHom) hclosed C hC centers hcenterInv
      rN hr hr1 φ K hφ hsource hInv hcover ψ (Fintype.card ι * A / rN) hsmooth hrange hone hzero hLip
  have hmono (B : ℕ) (hB : 2 ≤ B) (hBT : B ≤ T) :
      Real.exp ((p + B) ^ B) ≤ Real.exp ((p + T) ^ T) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hp (by omega) hBT)
  have hDT : D₀ ≤ T := by dsimp [T]; omega
  have h0T := hmono D₀ hD₀ hDT
  have hshift := shifted_center_power_bound D₀ D₁ hp
  have hCT : (C : ℝ) ≤ Real.exp ((p + T) ^ T) :=
    (hCb.trans (Real.exp_le_exp.mpr hshift)).trans
      (hmono (D₀ + D₁ + 2) (by omega) (by dsimp [T]; omega))
  have hBunit : ((1 : ℝ≥0) : ℝ) ≤ Real.exp ((p + 2) ^ 0) := by
    simpa only [NNReal.coe_one, pow_zero] using Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
  have hBT : (bchLogMetricConstant s (Fintype.card ι) H 1 : ℝ) ≤ Real.exp ((p + T) ^ T) :=
    (NNReal.coe_le_coe.mpr (bchLogMetricConstant_le_inverseBoxConstant _ _ _)).trans
      ((hinverse _ H 1 p hp hd hH hBunit).trans (hmono D₂ hD₂ (by dsimp [T]; omega)))
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hbase : p + T ≤ (p + T) ^ T := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + T) (by omega : 1 ≤ T)
  have hdT : (Fintype.card ι : ℝ) ≤ Real.exp ((p + T) ^ T) := by
    linarith [Real.add_one_le_exp ((p + T) ^ T)]
  have hAT : (A : ℝ) ≤ Real.exp ((p + T) ^ T) := by
    have hNT : (N : ℝ) ≤ T := by exact_mod_cast (show N ≤ T by dsimp [T]; omega)
    linarith [Real.add_one_le_exp ((p + T) ^ T)]
  let P : ℝ≥0 := (n + 1) * ((Fintype.card ι * A / rN) * K +
    1 / (rN / (4 * (C * bchLogMetricConstant s (Fintype.card ι) H 1 ^ 2))))
  have hP : (P : ℝ) ≤ Real.exp ((p + D) ^ D) :=
    smooth_partition_power_budget T n (Fintype.card ι) hT A K C _ rN hp
      (hnb.trans h0T) hdT hAT (hK.trans h0T) hCT hBT (hri.trans h0T)
  have h0D : Real.exp ((p + D₀) ^ D₀) ≤ Real.exp ((p + D) ^ D) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hp (by omega) (by dsimp [D]; omega))
  refine ⟨rN, hr, hr1, hri.trans h0D, n, hn, hnb.trans h0D, centers, φ,
    fun j i => (hcenters j i).trans h0D, hφ, hsource, ?_, P, hP, f,
    hfrange, hfsum, hfsupport, ?_, ?_, hfInner, K, hK.trans h0D, hForward⟩
  · exact fun j => realification_quotient_chart_mem_maximalAtlas e Γ l hl houter hc
      (centers j) (φ j) (hφ j) ∞
  · exact fun j => (contMDiff_realification_quotient_iff e Γ l hl houter hc ∞ (f j)).mpr (hfsmooth j)
  · simpa only [Fintype.card_fin] using hfLip

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeChartPartition
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

theorem exists_native_chart_partition (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      letI := D.metricSpace
      ∃ r : ℝ≥0, 0 < r ∧ r ≤ 1 ∧ 1 / (r : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        ∃ centers : Fin n → D.RealGroup,
        ∃ phi : Fin n → OpenPartialHomeomorph (Fin d → ℝ) D.Space,
          (∀ j i, |(D.basis.baseChange ℝ).repr (centers j).coord i| ≤ Real.exp ((p + 2) ^ C)) ∧
          (∀ j v, phi j v = QuotientGroup.mk
            (centers j * (NilpotentLieBCHGroup.basisHomeomorph (D.basis.baseChange ℝ)).symm v)) ∧
          (∀ j, (phi j).source = {v | ∀ i, |v i| < (r : ℝ)}) ∧
          ∃ P : ℝ≥0, (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
          ∃ f : Fin n → D.Space → ℝ,
            (∀ j x, 0 ≤ f j x ∧ f j x ≤ 1) ∧ (∀ x, ∑ j, f j x = 1) ∧
            (∀ j, HasCompactSupport (f j) ∧ tsupport (f j) ⊆ (phi j).target) ∧
            (∀ j, LipschitzWith P (f j)) ∧
            (∀ j, tsupport (f j) ⊆ phi j '' Metric.closedBall 0 (3 * (r : ℝ) / 4)) ∧
            ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
              ∀ j, LipschitzOnWith K (phi j) (phi j).source := by
  obtain ⟨A, _, hpartition⟩ := exists_realification_smooth_partition_exp_bound s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    ((Polynomial.X + 1 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro L _ _ d _ _ _ _ D p hp hD
  let := D.metricSpace
  let H := ⌈Real.exp p⌉₊
  have hc (i j k) : RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  obtain ⟨r, hr, hr1, hri, n, hn, hnb, centers, phi, hcenters, hphi, hsource, _,
    P, hP, f, hfrange, hfsum, hfsupport, _, hfLip, hfInner, K, hK, hForward⟩ :=
    hpartition D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid H (p + 1)
      D.grid_pos D.inner_grid D.outer_grid hc (by linarith)
      (by simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith))
      (ceil_exp_le_exp_add_one hp)
      (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  have hb : (p + 1 + A) ^ A ≤ (p + 2) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have heb := Real.exp_le_exp.mpr hb
  exact ⟨r, hr, hr1, hri.trans heb, n, hn, hnb.trans heb, centers, phi,
    fun j i => (hcenters j i).trans heb, hphi, hsource, P, hP.trans heb,
    f, hfrange, hfsum, hfsupport, hfLip, hfInner, K, hK.trans heb, hForward⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PositivePartitionScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_weighted_partition_score {Ω ι : Type*} [Fintype Ω] [Fintype ι] [Nonempty ι]
    (a : Ω → ℝ) (w : ι → Ω → ℝ) (hsum : ∀ x, ∑ i, w i x = 1)
    {S : ℝ} (hS : S ≤ 𝔼 x, a x) :
    ∃ i, S / Fintype.card ι ≤ 𝔼 x, a x * w i x := by
  have htotal : (∑ i, 𝔼 x, a x * w i x) = 𝔼 x, a x := by
    rw [← Finset.expect_sum_comm]
    apply Finset.expect_congr rfl
    intro x _
    rw [← Finset.mul_sum, hsum, mul_one]
  have hmean : (𝔼 i, 𝔼 x, a x * w i x) = (𝔼 x, a x) / Fintype.card ι := by
    rw [Fintype.expect_eq_sum_div_card, htotal]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty
    (show S / Fintype.card ι ≤ 𝔼 i, 𝔼 x, a x * w i x from
      hmean.symm ▸ div_le_div_of_nonneg_right hS (Nat.cast_nonneg _))
  exact ⟨i, hi⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d n : ℕ}
  (D : RationalFilteredNilmanifold L s d) (I : LieIdeal ℚ L)
  (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
  (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
  (hQF : Q.filtration = D.filtration.quotientLie I hI)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ I))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ I))] [T2Space (ℝ ⊗[ℚ] (L ⧸ I))]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ K Ξ : Type*} [LieRing K] [LieAlgebra ℚ K] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
  (D : RationalFilteredNilmanifold K s d) {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (T : D.Niltest w) (hT : T.UnitIntervalValued)
  (psi : D.Space → ℝ) (hpsi : ∀ z, 0 ≤ psi z ∧ psi z ≤ 1)
  (K : ℝ≥0) (hLip : letI := D.metricSpace; LipschitzWith K psi)

theorem positiveLocalization_unit_interval :
    (T.positiveLocalization hT psi hpsi K hLip).UnitIntervalValued := by
  intro z
  exact ⟨rfl, mul_nonneg (hT z).2.1 (hpsi z).1,
    (mul_le_of_le_one_right (hT z).2.1 (hpsi z).2).trans (hT z).2.2⟩

theorem positiveLocalization_eval_re (x : σ → ℤ) :
    ((T.positiveLocalization hT psi hpsi K hLip).eval x).re =
      (T.eval x).re * psi (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval w x T.orbit)) := rfl

theorem positiveLocalization_support :
    tsupport (T.positiveLocalization hT psi hpsi K hLip).observable ⊆ tsupport psi := by
  apply closure_mono
  intro z hz
  change psi z ≠ 0
  intro hzero
  apply hz
  change (((T.observable z).re * psi z : ℝ) : ℂ) = 0
  rw [hzero, mul_zero, Complex.ofReal_zero]

theorem positiveLocalization_complexity {p : ℝ} (hp : 0 ≤ p)
    (hcomplexity : T.ComplexityLE p) (hK : (K : ℝ) ≤ Real.exp p) :
    (T.positiveLocalization hT psi hpsi K hLip).ComplexityLE (p + 4) := by
  refine ⟨hcomplexity.1.mono D (by linarith), ?_⟩
  change Real.log (2 + (1 : ℝ) + ((T.lipBound + K : ℝ≥0) : ℝ)) ≤ p + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  rw [NNReal.coe_add, Real.exp_add]
  have hbudget := observable_budget hcomplexity
  have hnorm := T.normBound.coe_nonneg
  have hone := Real.one_le_exp hp
  have hfive : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hprod := mul_le_mul_of_nonneg_right hfive (Real.exp_nonneg p)
  nlinarith

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.IntegralScoredKernel
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

theorem exists_scored_native_chart_oai (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ X L : Type*} [Fintype X]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      (a : X → ℝ) (u : X → σ → ℤ) {p : ℝ},
      0 ≤ p → T.ComplexityLE p → T.UnitIntervalValued →
      Real.exp (-p) ≤ (𝔼 x, a x * (T.eval (u x)).re) →
      letI := D.metricSpace
      ∃ (r : ℝ≥0) (z : D.RealGroup) (phi : OpenPartialHomeomorph (Fin d → ℝ) D.Space),
        0 < r ∧ r ≤ 1 ∧ 1 / (r : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ i, |(D.basis.baseChange ℝ).repr z.coord i| ≤ Real.exp ((p + 2) ^ C)) ∧
        (∀ v, phi v = QuotientGroup.mk
          (z * (NilpotentLieBCHGroup.basisHomeomorph (D.basis.baseChange ℝ)).symm v)) ∧
        phi.source = {v | ∀ i, |v i| < (r : ℝ)} ∧
        ∃ U : D.Niltest w, U.orbit = T.orbit ∧ U.UnitIntervalValued ∧
          U.ComplexityLE ((p + 2) ^ C) ∧ HasCompactSupport U.observable ∧
          tsupport U.observable ⊆ phi.target ∧
          (Real.exp (-((p + 2) ^ C)) ≤ 𝔼 x, a x * (U.eval (u x)).re) ∧
          tsupport U.observable ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4) ∧
          ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
            LipschitzOnWith K phi phi.source := by
  obtain ⟨A, hA, hpartition⟩ := exists_native_chart_partition s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (Polynomial.X + (Polynomial.X + 2) ^ A + 4)
  refine ⟨C, hC, ?_⟩
  intro σ X L _ _ _ d _ _ _ _ D w T a u p hp hT hpositive hscore
  let := D.metricSpace
  obtain ⟨r, hr, hr1, hri, n, hn, hnb, centers, phi, hcenters, hphi, hsource,
    P, hP, f, hfrange, hfsum, hfsupport, hfLip, hfInner, K, hK, hForward⟩ := hpartition D hp hT.1
  let q : ℝ := (p + 2) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by omega)
  have hb : p + q + 4 ≤ (p + 2) ^ C := by
    simpa [q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + 2) ^ C := by linarith
  let point : X → D.Space := fun x => QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval w (u x) T.orbit)
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, hj⟩ := exists_weighted_partition_score
    (fun x => a x * (T.eval (u x)).re) (fun j x => f j (point x))
    (fun x => hfsum (point x)) hscore
  let U := T.positiveLocalization hpositive (f j) (hfrange j) P (hfLip j)
  have hU : U.ComplexityLE ((p + 2) ^ C) :=
    (T.positiveLocalization_complexity hpositive (f j) (hfrange j) P (hfLip j)
      hq (hT.mono hpq) hP).mono (by linarith)
  have hsupp : tsupport U.observable ⊆ tsupport (f j) :=
    T.positiveLocalization_support hpositive (f j) (hfrange j) P (hfLip j)
  refine ⟨r, centers j, phi j, hr, hr1, hri.trans (Real.exp_le_exp.mpr hqC),
    fun i => (hcenters j i).trans (Real.exp_le_exp.mpr hqC), hphi j, hsource j,
    U, rfl, T.positiveLocalization_unit_interval hpositive (f j) (hfrange j) P (hfLip j),
    hU, (hfsupport j).1.of_isClosed_subset isClosed_closure hsupp,
    hsupp.trans (hfsupport j).2, ?_, hsupp.trans (hfInner j), K,
    hK.trans (Real.exp_le_exp.mpr hqC), hForward j⟩
  have hnj : (0 : ℝ) < n := by exact_mod_cast hn
  have hscoreU : Real.exp (-p) / n ≤ 𝔼 x, a x * (U.eval (u x)).re := by
    simpa only [Fintype.card_fin, U, Niltest.positiveLocalization_eval_re,
      point, mul_assoc] using hj
  calc
    _ ≤ Real.exp (-p - q) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-p) / Real.exp q := Real.exp_sub _ _
    _ ≤ Real.exp (-p) / n := div_le_div_of_nonneg_left (Real.exp_nonneg _) hnj hnb
    _ ≤ _ := hscoreU

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal BigOperators

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.RationalFilteredNilmanifold.exists_scored_native_chart_oai.{u_1, u_2, u_3} := @OAI.Erdos3.RationalFilteredNilmanifold.exists_scored_native_chart_oai.{u_1, u_2, u_3}
