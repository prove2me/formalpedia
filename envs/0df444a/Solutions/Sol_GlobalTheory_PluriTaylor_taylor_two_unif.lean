-- Prove2me | solution 1 for GlobalTheory.PluriTaylor.taylor_two_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:27:09.334694+00:00
-- url     : https://prove2.me/submissions/c7a993c0-6a00-47bf-8e73-65c931fffb0d

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformTaylorBoundLeviPluriharmonicSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.PluriTaylor
open Set
variable {n : ℕ}
namespace GlobalTheory.PluriTaylor
theorem _root_.solution (U K : Set (V n)) (φ : V n → ℝ) (η : ℝ) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, closedBall z δ ⊆ U ∧ ∀ w ∈ closedBall (0 : V n) δ,
      φ (z + w) ≤ φ z + fderiv ℝ φ z w + (1 / 2) * fderiv ℝ (fderiv ℝ φ) z w w + η * ‖w‖ ^ 2 := by
  obtain ⟨δ₀, hδ₀, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening δ₀ K) := hK.cthickening
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_num)
  have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ φ)) U :=
    (h1.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn
  obtain ⟨δ₁, hδ₁, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (hK'.uniformContinuousOn_of_continuous (h2.mono hsub)) η hη
  refine ⟨min δ₀ (δ₁ / 2), lt_min hδ₀ (half_pos hδ₁), fun z hz => ?_⟩
  have hball : closedBall z (min δ₀ (δ₁ / 2)) ⊆ U :=
    (closedBall_subset_closedBall (min_le_left _ _)).trans
      ((closedBall_subset_cthickening hz δ₀).trans hsub)
  refine ⟨hball, fun w hw => ?_⟩
  rw [mem_closedBall, dist_zero_right] at hw
  set f1 := fderiv ℝ φ
  set f2 := fderiv ℝ f1
  have hpt : ∀ t ∈ Icc (0:ℝ) 1, z + t • w ∈ closedBall z (min δ₀ (δ₁ / 2)) := by
    intro t ht
    rw [mem_closedBall, dist_self_add_left, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hw
  have hnhds : ∀ t ∈ Icc (0:ℝ) 1, U ∈ 𝓝 (z + t • w) := fun t ht =>
    hU.mem_nhds (hball (hpt t ht))
  have hpath : ∀ t : ℝ, HasDerivAt (fun s : ℝ => z + s • w) w t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const w).const_add z
  have hg : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt (fun s : ℝ => φ (z + s • w)) (f1 (z + t • w) w) t := by
    intro t ht
    have hd : DifferentiableAt ℝ φ (z + t • w) :=
      (hφ.contDiffAt (hnhds t ht)).differentiableAt (by norm_num)
    exact hd.hasFDerivAt.comp_hasDerivAt t (hpath t)
  have hg1 : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => f1 (z + s • w) w) (f2 (z + t • w) w w) t := by
    intro t ht
    have hd : DifferentiableAt ℝ f1 (z + t • w) :=
      (h1.contDiffAt (hnhds t ht)).differentiableAt (by norm_num)
    have hc : HasDerivAt (fun s : ℝ => f1 (z + s • w)) (f2 (z + t • w) w) t :=
      hd.hasFDerivAt.comp_hasDerivAt t (hpath t)
    have hw0 : HasDerivAt (fun _ : ℝ => w) (0 : V n) t := hasDerivAt_const t w
    have := hc.clm_apply hw0
    simpa using this
  have hclose : ∀ t ∈ Icc (0:ℝ) 1, ‖f2 (z + t • w) - f2 z‖ ≤ η := by
    intro t ht
    have hz' : z ∈ cthickening δ₀ K := self_subset_cthickening K hz
    have hy : z + t • w ∈ cthickening δ₀ K :=
      closedBall_subset_cthickening hz δ₀
        (closedBall_subset_closedBall (min_le_left _ _) (hpt t ht))
    have hd : dist (z + t • w) z < δ₁ := by
      have := hpt t ht
      rw [mem_closedBall] at this
      linarith [min_le_right δ₀ (δ₁ / 2)]
    have := hunif _ hy _ hz' hd
    rw [dist_eq_norm] at this
    exact this.le
  have hud : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt
      (fun s : ℝ => f1 (z + s • w) w - f1 z w - s * f2 z w w)
      (f2 (z + t • w) w w - f2 z w w) (Icc 0 1) t := by
    intro t ht
    have := ((hg1 t ht).sub_const (f1 z w)).sub ((hasDerivAt_id t).mul_const (f2 z w w))
    exact (this.congr_deriv (by simp)).hasDerivWithinAt
  have hbd : ∀ t ∈ Ico (0:ℝ) 1, ‖f2 (z + t • w) w w - f2 z w w‖ ≤ η * ‖w‖ ^ 2 := by
    intro t ht
    have hT := hclose t (Ico_subset_Icc_self ht)
    calc ‖f2 (z + t • w) w w - f2 z w w‖ = ‖(f2 (z + t • w) - f2 z) w w‖ := by
          simp only [ContinuousLinearMap.sub_apply]
      _ ≤ ‖f2 (z + t • w) - f2 z‖ * ‖w‖ * ‖w‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ η * ‖w‖ * ‖w‖ := by gcongr
      _ = η * ‖w‖ ^ 2 := by ring
  have hu : ∀ t ∈ Icc (0:ℝ) 1, ‖f1 (z + t • w) w - f1 z w - t * f2 z w w‖ ≤ η * ‖w‖ ^ 2 := by
    intro t ht
    have := norm_image_sub_le_of_norm_deriv_le_segment' hud hbd t ht
    simp only [zero_smul, add_zero, sub_self, zero_mul, sub_zero] at this
    exact this.trans (mul_le_of_le_one_right (mul_nonneg hη.le (sq_nonneg _)) ht.2)
  have hGd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt
      (fun s : ℝ => φ (z + s • w) - φ z - s * f1 z w - s ^ 2 / 2 * f2 z w w)
      (f1 (z + t • w) w - f1 z w - t * f2 z w w) (Icc 0 1) t := by
    intro t ht
    have := (((hg t ht).sub_const (φ z)).sub ((hasDerivAt_id t).mul_const (f1 z w))).sub
      (((hasDerivAt_pow 2 t).div_const 2).mul_const (f2 z w w))
    exact (this.congr_deriv (by norm_num)).hasDerivWithinAt
  have hG := norm_image_sub_le_of_norm_deriv_le_segment' hGd
    (fun t ht => hu t (Ico_subset_Icc_self ht)) 1 ⟨zero_le_one, le_rfl⟩
  simp only [one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_self, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, mul_one] at hG
  have hab := (Real.le_norm_self _).trans hG
  linarith
end GlobalTheory.PluriTaylor
