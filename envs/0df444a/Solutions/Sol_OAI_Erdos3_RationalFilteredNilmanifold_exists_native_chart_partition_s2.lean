-- Prove2me | solution 1 for OAI.Erdos3.RationalFilteredNilmanifold.exists_native_chart_partition_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:10:58.232977+00:00
-- url     : https://prove2.me/submissions/f7fae723-dae5-48bc-88d0-6356cc23c765

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B065
import Definitions.Def_OAIE3v2B110
import Definitions.Def_OAIE3v2B115
import Definitions.Def_OAIE3v2B122
import Theorems.Thm_OAI_Erdos3_exists_realification_finite_bilipschitz_atlas_exp_bound_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedCutoffs
namespace OAI

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHChartCutoffSmooth
namespace OAI

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHLatticeImageGap
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealifiedBCHSmoothPartition
namespace OAI

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
  obtain ⟨D₀, hD₀, hatlas⟩ := exists_realification_finite_bilipschitz_atlas_exp_bound_s2 s
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

theorem exists_native_chart_partition_s2_oai (s : ℕ) :
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

theorem solution.{u_1} : type_of% @OAI.Erdos3.RationalFilteredNilmanifold.exists_native_chart_partition_s2_oai.{u_1} := @OAI.Erdos3.RationalFilteredNilmanifold.exists_native_chart_partition_s2_oai.{u_1}
