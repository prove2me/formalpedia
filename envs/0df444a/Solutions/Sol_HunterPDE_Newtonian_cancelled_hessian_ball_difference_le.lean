-- Prove2me | solution 1 for HunterPDE.Newtonian.cancelled_hessian_ball_difference_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T18:54:47.072521+00:00
-- url     : https://prove2.me/submissions/a25b7b43-5a9a-4cca-b17d-ed8c9e9cd8e3

import Theorems.Thm_HunterPDE_Newtonian_cancelled_hessian_near_bound
import Theorems.Thm_HunterPDE_Newtonian_cancelled_hessian_far_bound
import Theorems.Thm_HunterPDE_Newtonian_integral_secondPartial_annulus_eq_zero
import Theorems.Thm_HunterPDE_Newtonian_secondPartial_formula
import Theorems.Thm_HunterPDE_Newtonian_norm_secondPartial_le
import Theorems.Thm_HunterPDE_Newtonian_norm_fderiv_secondPartial_le
import Theorems.Thm_MeasureTheory_singularKernel_holder_near_bound
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Module

open MeasureTheory HunterPDE.Newtonian Metric Set
open scoped ContDiff NNReal
set_option autoImplicit false

noncomputable section
namespace CancelledDiffWork

variable {n : ℕ}

/-- The Hessian kernel of `Γ` is continuous away from the origin. -/
theorem kernel_continuousAt (hn : 2 ≤ n) (i j : Fin n) (z : EuclideanSpace ℝ (Fin n))
    (hz : z ≠ 0) : ContinuousAt (secondPartial (fundamentalSolution n) i j) z := by
  obtain ⟨C, -, hC⟩ := norm_fderiv_secondPartial_le n hn
  exact (hC i j z hz).1.continuousAt

theorem kernel_measurable (hn : 2 ≤ n) (i j : Fin n) :
    Measurable (secondPartial (fundamentalSolution n) i j) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro z hz
  exact (kernel_continuousAt hn i j z hz).continuousWithinAt

/-- The Hessian kernel of `Γ` is even. -/
theorem kernel_neg (hn : 2 ≤ n) (i j : Fin n) (z : EuclideanSpace ℝ (Fin n)) :
    secondPartial (fundamentalSolution n) i j (-z) =
      secondPartial (fundamentalSolution n) i j z := by
  by_cases hz : z = 0
  · simp [hz]
  rw [secondPartial_formula n hn i j (-z) (neg_ne_zero.mpr hz),
    secondPartial_formula n hn i j z hz]
  simp only [norm_neg, PiLp.neg_apply]
  ring

/-- Change of variables `y ↦ a - y` for set integrals. -/
theorem setIntegral_reflect (a : EuclideanSpace ℝ (Fin n)) (S T : Set (EuclideanSpace ℝ (Fin n)))
    (hS : MeasurableSet S) (hT : MeasurableSet T) (Φ Ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hST : ∀ y, a - y ∈ S ↔ y ∈ T) (hΦ : ∀ y, Φ (a - y) = Ψ y) :
    (∫ y in S, Φ y) = ∫ y in T, Ψ y := by
  rw [← integral_indicator hS, ← integral_indicator hT,
    ← integral_sub_left_eq_self (S.indicator Φ) volume a]
  congr 1
  ext y
  by_cases hy : y ∈ T
  · rw [indicator_of_mem ((hST y).2 hy), indicator_of_mem hy, hΦ]
  · rw [indicator_of_notMem (fun h => hy ((hST y).1 h)), indicator_of_notMem hy]

theorem integrableOn_reflect (a : EuclideanSpace ℝ (Fin n)) (S T : Set (EuclideanSpace ℝ (Fin n)))
    (hS : MeasurableSet S) (hT : MeasurableSet T) (Φ Ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hST : ∀ y, a - y ∈ S ↔ y ∈ T) (hΦ : ∀ y, Φ (a - y) = Ψ y) (h : IntegrableOn Φ S) :
    IntegrableOn Ψ T := by
  rw [← integrable_indicator_iff hT]
  rw [← integrable_indicator_iff hS] at h
  refine (h.comp_sub_left a).congr (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ T
  · simp only [indicator_of_mem ((hST y).2 hy), indicator_of_mem hy, hΦ]
  · simp only [indicator_of_notMem (fun h => hy ((hST y).1 h)), indicator_of_notMem hy]

/-- Singular-kernel estimate on a measurable piece of a ball centred at the singularity. -/
theorem near_piece (hn : 2 ≤ n) (α : ℝ) (hα : 0 < α) (i j : Fin n) (Cb : ℝ) (hCb : 0 ≤ Cb)
    (hb : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 →
      ‖secondPartial (fundamentalSolution n) i j z‖ ≤ Cb * ‖z‖ ^ (-(n : ℝ)))
    (p : EuclideanSpace ℝ (Fin n)) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : MeasurableSet S)
    (r : ℝ) (hr : 0 < r) (hSr : S ⊆ ball p r) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hgm : Measurable g) (G : ℝ) (hG : 0 ≤ G) (hg : ∀ y ∈ S, |g y| ≤ G * ‖p - y‖ ^ α) :
    IntegrableOn (fun y => secondPartial (fundamentalSolution n) i j (p - y) * g y) S ∧
      |∫ y in S, secondPartial (fundamentalSolution n) i j (p - y) * g y| ≤
        ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * Cb / α) * G *
          r ^ α := by
  set K := secondPartial (fundamentalSolution n) i j with hK
  have hKm : AEStronglyMeasurable K volume := (kernel_measurable hn i j).aestronglyMeasurable
  let g' : EuclideanSpace ℝ (Fin n) → ℝ := fun z => S.indicator g (p - z)
  have hgm' : AEStronglyMeasurable g' volume :=
    ((hgm.indicator hS).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hg' : ∀ z, |g' z| ≤ G * ‖z‖ ^ α := by
    intro z
    by_cases hz : p - z ∈ S
    · simp only [g', indicator_of_mem hz]
      simpa only [sub_sub_cancel] using hg (p - z) hz
    · simp only [g', indicator_of_notMem hz, abs_zero]
      positivity
  obtain ⟨hi, he⟩ := MeasureTheory.singularKernel_holder_near_bound n (by omega) α hα
    K g' hKm hgm' Cb G hCb hG hb hg' r hr
  have hm := Measure.measurePreserving_sub_left (volume : Measure (EuclideanSpace ℝ (Fin n))) p
  have hemb := (Homeomorph.subLeft p).measurableEmbedding
  have hs : (fun y => p - y) ⁻¹' ball 0 r = ball p r := by
    ext y
    simp only [mem_preimage, mem_ball, dist_eq_norm, sub_zero]
    rw [norm_sub_rev]
  have hit := (hm.integrableOn_comp_preimage hemb).2 hi
  have het := hm.setIntegral_preimage_emb hemb (fun z => K z * g' z) (ball 0 r)
  simp only [hs, Function.comp_def, g', sub_sub_cancel] at hit het
  have hfun : (fun y => K (p - y) * S.indicator g y) =
      S.indicator (fun y => K (p - y) * g y) := by
    ext y
    by_cases hy : y ∈ S
    · simp [indicator_of_mem hy]
    · simp [indicator_of_notMem hy]
  rw [hfun] at hit het
  have hSS : S ∩ ball p r = S := inter_eq_left.mpr hSr
  refine ⟨?_, ?_⟩
  · have := (integrable_indicator_iff hS).1 hit
    rwa [IntegrableOn, Measure.restrict_restrict hS, hSS] at this
  · rw [setIntegral_indicator hS, inter_comm, hSS] at het
    rw [het]
    calc _ ≤ _ := he
      _ = _ := by ring

end CancelledDiffWork

open CancelledDiffWork

theorem solution (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ f → HasCompactSupport f →
      ∀ H : ℝ≥0, (∀ x y, |f x - f y| ≤ (H : ℝ) * ‖x - y‖ ^ α) →
      ∀ x x' : EuclideanSpace ℝ (Fin n), ∀ R : ℝ, 0 < R →
        tsupport f ⊆ Metric.ball x R → tsupport f ⊆ Metric.ball x' R →
        ∀ i j : Fin n,
          |(∫ y in Metric.ball x R,
              secondPartial (fundamentalSolution n) i j (x - y) * (f y - f x)) -
            (∫ y in Metric.ball x' R,
              secondPartial (fundamentalSolution n) i j (x' - y) * (f y - f x'))| ≤
            (A : ℝ) * (H : ℝ) * ‖x - x'‖ ^ α := by
  classical
  obtain ⟨Anear, hnear⟩ := cancelled_hessian_near_bound n hn α hα₀
  obtain ⟨Afar, hAfar0, hfar⟩ := cancelled_hessian_far_bound n hn α hα₀ hα₁
  choose C hC hbound using (fun p : Fin n × Fin n => norm_secondPartial_le n hn p.1 p.2)
  let M : ℝ := ∑ p, C p
  have hM : 0 ≤ M := Finset.sum_nonneg (fun p _ => hC p)
  let Q : ℝ := (n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * M / α
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let A : ℝ := 8 * Q + Afar + 4 * (Anear : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨(⟨A, hA⟩ : ℝ≥0), ?_⟩
  intro f hf hfc H hH x x' R hR hsx hsx' i j
  change _ ≤ A * (H : ℝ) * ‖x - x'‖ ^ α
  have hfcont : Continuous f := hf.continuous
  set K := secondPartial (fundamentalSolution n) i j with hKdef
  have hKm : Measurable K := kernel_measurable hn i j
  have hKneg : ∀ z, K (-z) = K z := kernel_neg hn i j
  have hHn : (0 : ℝ) ≤ H := H.coe_nonneg
  have hCM : C (i, j) ≤ M := Finset.single_le_sum (fun p _ => hC p) (Finset.mem_univ _)
  have hb : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → ‖K z‖ ≤ M * ‖z‖ ^ (-(n : ℝ)) := by
    intro z hz
    exact (hbound (i, j) z hz).trans
      (mul_le_mul_of_nonneg_right hCM (Real.rpow_nonneg (norm_nonneg z) _))
  rcases eq_or_ne x x' with hxx | hxx
  · subst hxx
    simp [Real.zero_rpow hα₀.ne']
  set δ := ‖x - x'‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr hxx)
  set t := δ ^ α with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hδ.le _
  have h2α : (2 : ℝ) ^ α ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα₁.le
  have h2δ : (2 * δ) ^ α ≤ 2 * t := by
    rw [Real.mul_rpow (by norm_num) hδ.le]
    exact mul_le_mul_of_nonneg_right h2α ht0
  have hHt : 0 ≤ (H : ℝ) * t := mul_nonneg hHn ht0
  by_cases hbig : 2 * R ≤ 3 * δ
  · -- Small radius: each integral is bounded separately.
    have h1 := (hnear f hfcont H hH x R hR i j).2
    have h2 := (hnear f hfcont H hH x' R hR i j).2
    have hRα : R ^ α ≤ 2 * t := by
      calc R ^ α ≤ (2 * δ) ^ α := Real.rpow_le_rpow hR.le (by linarith) hα₀.le
        _ ≤ 2 * t := h2δ
    have hAH : 0 ≤ (Anear : ℝ) * H := mul_nonneg Anear.coe_nonneg hHn
    have h3 : (Anear : ℝ) * H * R ^ α ≤ (Anear : ℝ) * H * (2 * t) :=
      mul_le_mul_of_nonneg_left hRα hAH
    calc _ ≤ _ := abs_sub _ _
      _ ≤ (Anear : ℝ) * H * (2 * t) + (Anear : ℝ) * H * (2 * t) := by linarith
      _ = (4 * (Anear : ℝ)) * (H * t) := by ring
      _ ≤ A * (H * t) := by
          apply mul_le_mul_of_nonneg_right _ hHt
          dsimp [A]; linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hQ]
      _ = A * H * t := by ring
  push_neg at hbig
  -- Geometry: midpoint `m`, half-step `h`.
  set h : EuclideanSpace ℝ (Fin n) := (1 / 2 : ℝ) • (x - x') with hhdef
  set m : EuclideanSpace ℝ (Fin n) := x' + h with hmdef
  have hmx : m + h = x := by simp only [hmdef, hhdef]; module
  have hmx' : m - h = x' := by simp only [hmdef]; abel
  have hnh : ‖h‖ = δ / 2 := by
    rw [hhdef, norm_smul, hδdef]; norm_num; ring
  have hdxm : dist x m = δ / 2 := by
    rw [dist_eq_norm, ← hmx]; simp [hnh]
  have hdx'm : dist x' m = δ / 2 := by
    rw [dist_eq_norm, ← hmx', show m - h - m = -h by abel, norm_neg, hnh]
  have hrefl : ∀ y, (x + x' - y) - m = m - y := by
    intro y; rw [← hmx, ← hmx']; abel
  set B := closedBall m δ with hBdef
  set E := (closedBall m δ)ᶜ with hEdef
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hEm : MeasurableSet E := measurableSet_closedBall.compl
  -- The common decomposition, for `p ∈ {x, x'}`.
  have key : ∀ p : EuclideanSpace ℝ (Fin n), dist p m = δ / 2 → tsupport f ⊆ ball p R →
      IntegrableOn (fun y => K (p - y) * f y) E ∧
      (∫ y in ball p R, K (p - y) * (f y - f p)) =
        (∫ y in B, K (p - y) * (f y - f p)) + (∫ y in E, K (p - y) * f y) +
          f p * ∫ y in B \ closedBall p (δ / 2), K (p - y) := by
    intro p hpm hsp
    have hI := (hnear f hfcont H hH p R hR i j).1
    have hBsub : B ⊆ ball p R := by
      intro y hy
      rw [mem_ball]
      have := dist_triangle y m p
      rw [mem_closedBall] at hy
      rw [dist_comm m p, hpm] at this
      linarith
    have hcbB : closedBall p (δ / 2) ⊆ B := by
      intro y hy
      rw [mem_closedBall] at hy ⊢
      have := dist_triangle y p m
      linarith
    let Kc := closedBall p R \ ball p (δ / 2)
    have hKc : IntegrableOn (fun y => K (p - y)) Kc := by
      apply ContinuousOn.integrableOn_compact (isCompact_closedBall p R |>.diff isOpen_ball)
      intro y hy
      have hne : p - y ≠ 0 := by
        intro h0
        have : y = p := (sub_eq_zero.mp h0).symm
        apply hy.2
        rw [this, mem_ball, dist_self]; linarith
      exact ((kernel_continuousAt hn i j _ hne).comp
        (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
    set D := ball p R \ B with hDdef
    have hDm : MeasurableSet D := measurableSet_ball.diff hBm
    have hDKc : D ⊆ Kc := by
      intro y hy
      refine ⟨ball_subset_closedBall hy.1, ?_⟩
      intro hyb
      apply hy.2
      rw [mem_closedBall]
      rw [mem_ball] at hyb
      have := dist_triangle y p m
      linarith
    have hSKc : B \ closedBall p (δ / 2) ⊆ Kc := by
      intro y hy
      exact ⟨ball_subset_closedBall (hBsub hy.1),
        fun h' => hy.2 (ball_subset_closedBall h')⟩
    have hKD : IntegrableOn (fun y => K (p - y)) D := hKc.mono_set hDKc
    have hKfD : IntegrableOn (fun y => K (p - y) * f y) D := by
      refine ((hI.mono_set diff_subset).add (hKD.mul_const (f p))).congr_fun ?_ hDm
      intro y _; simp only [Pi.add_apply]; ring
    have hzero : ∀ y ∈ E \ D, K (p - y) * f y = 0 := by
      intro y hy
      have hyb : y ∉ ball p R := fun h' => hy.2 ⟨h', hy.1⟩
      rw [image_eq_zero_of_notMem_tsupport (fun h' => hyb (hsp h')), mul_zero]
    have hDE : D ⊆ E := fun y hy => hy.2
    refine ⟨hKfD.of_forall_diff_eq_zero hEm hzero, ?_⟩
    have s1 := integral_inter_add_diff hBm hI
    rw [inter_eq_right.mpr hBsub] at s1
    have s2 : (∫ y in D, K (p - y) * (f y - f p)) =
        (∫ y in D, K (p - y) * f y) - (∫ y in D, K (p - y)) * f p := by
      rw [← integral_mul_const, ← integral_sub hKfD (hKD.mul_const _)]
      congr 1; ext y; ring
    have s3 : (∫ y in E, K (p - y) * f y) = ∫ y in D, K (p - y) * f y :=
      setIntegral_eq_of_subset_of_forall_diff_eq_zero hEm hDE hzero
    have s4 : (∫ y in D, K (p - y)) + ∫ y in B \ closedBall p (δ / 2), K (p - y) = 0 := by
      have hann := integral_secondPartial_annulus_eq_zero n hn p R (δ / 2) hR (by linarith)
        (by linarith) i j
      have hset : ball p R \ closedBall p (δ / 2) = D ∪ (B \ closedBall p (δ / 2)) := by
        ext y
        simp only [D, mem_diff, mem_union]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases hyB : y ∈ B
          · exact Or.inr ⟨hyB, h2⟩
          · exact Or.inl ⟨h1, hyB⟩
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨h1, fun h' => h2 (hcbB h')⟩
          · exact ⟨hBsub h1, h2⟩
      rw [hset, setIntegral_union _ (hBm.diff measurableSet_closedBall) hKD
        (hKc.mono_set hSKc)] at hann
      · exact hann
      · rw [Set.disjoint_left]
        intro y hy hy'
        exact hy.2 hy'.1
    have hD : (∫ y in D, K (p - y)) = -∫ y in B \ closedBall p (δ / 2), K (p - y) := by
      linarith
    rw [← s1, s2, s3, hD]
    ring
  obtain ⟨hGx, kx⟩ := key x hdxm hsx
  obtain ⟨hGx', kx'⟩ := key x' hdx'm hsx'
  -- Reflection through `m` swaps `x` and `x'`.
  have he : (∫ y in B \ closedBall x (δ / 2), K (x - y)) =
      ∫ y in B \ closedBall x' (δ / 2), K (x' - y) := by
    apply setIntegral_reflect (x + x') _ _ (hBm.diff measurableSet_closedBall)
      (hBm.diff measurableSet_closedBall)
    · intro y
      simp only [hBdef, mem_diff, mem_closedBall, dist_eq_norm, hrefl y]
      rw [show x + x' - y - x = x' - y by abel, norm_sub_rev m y, norm_sub_rev x' y]
    · intro y
      rw [show x - (x + x' - y) = -(x' - y) by abel, hKneg]
  have hphi0 : (∫ y in E, (K (x - y) - K (x' - y))) = 0 := by
    have hr := setIntegral_reflect (x + x') E E hEm hEm (fun y => K (x - y) - K (x' - y))
      (fun y => -(K (x - y) - K (x' - y))) ?_ ?_
    · rw [integral_neg] at hr; linarith
    · intro y
      simp only [hEdef, mem_compl_iff, mem_closedBall, dist_eq_norm, hrefl y]
      rw [norm_sub_rev m y]
    · intro y
      show K (x - (x + x' - y)) - K (x' - (x + x' - y)) = -(K (x - y) - K (x' - y))
      rw [show x - (x + x' - y) = -(x' - y) by abel, show x' - (x + x' - y) = -(x - y) by abel,
        hKneg, hKneg]
      ring
  -- Far field.
  have hh0 : h ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnh
    linarith
  obtain ⟨hFi, hFb⟩ := hfar f hfcont H hH m h hh0 i j
  have h2h : 2 * ‖h‖ = δ := by rw [hnh]; ring
  rw [h2h] at hFi hFb
  have hSE : ∀ y, m - y ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) δ)ᶜ ↔ y ∈ E := by
    intro y
    simp only [hEdef, mem_compl_iff, mem_closedBall, dist_eq_norm, sub_zero]
    rw [norm_sub_rev m y]
  have hΦ : ∀ y, (K ((m - y) + h) - K ((m - y) - h)) * (f (m - (m - y)) - f (m + h)) =
      (K (x - y) - K (x' - y)) * (f y - f x) := by
    intro y
    rw [show m - y + h = x - y by rw [← hmx]; abel,
      show m - y - h = x' - y by rw [← hmx']; abel, sub_sub_cancel, hmx]
  have hFiE := integrableOn_reflect m _ E measurableSet_closedBall.compl hEm
    (fun z => (K (z + h) - K (z - h)) * (f (m - z) - f (m + h)))
    (fun y => (K (x - y) - K (x' - y)) * (f y - f x)) hSE hΦ hFi
  have hFeq := setIntegral_reflect m _ E measurableSet_closedBall.compl hEm
    (fun z => (K (z + h) - K (z - h)) * (f (m - z) - f (m + h)))
    (fun y => (K (x - y) - K (x' - y)) * (f y - f x)) hSE hΦ
  rw [hFeq] at hFb
  have hGdiff : (∫ y in E, K (x - y) * f y) - (∫ y in E, K (x' - y) * f y) =
      ∫ y in E, (K (x - y) - K (x' - y)) * (f y - f x) := by
    have hφf : IntegrableOn (fun y => (K (x - y) - K (x' - y)) * f y) E :=
      (hGx.sub hGx').congr_fun (fun y _ => by simp only [Pi.sub_apply]; ring) hEm
    have hφc : IntegrableOn (fun y => (K (x - y) - K (x' - y)) * f x) E :=
      (hφf.sub hFiE).congr_fun (fun y _ => by simp only [Pi.sub_apply]; ring) hEm
    have hsplit : (fun y => (K (x - y) - K (x' - y)) * (f y - f x)) =
        fun y => (K (x - y) - K (x' - y)) * f y - (K (x - y) - K (x' - y)) * f x := by
      ext y; ring
    rw [← integral_sub hGx hGx', hsplit, integral_sub hφf hφc, integral_mul_const, hphi0,
      zero_mul, sub_zero]
    congr 1; ext y; ring
  -- Near field.
  have hBball : ∀ p : EuclideanSpace ℝ (Fin n), dist p m = δ / 2 → B ⊆ ball p (2 * δ) := by
    intro p hpm y hy
    rw [mem_ball]
    rw [hBdef, mem_closedBall] at hy
    have := dist_triangle y m p
    rw [dist_comm m p, hpm] at this
    linarith
  have hNx : |∫ y in B, K (x - y) * (f y - f x)| ≤ Q * H * (2 * δ) ^ α :=
    (near_piece hn α hα₀ i j M hM hb x B hBm (2 * δ) (by linarith) (hBball x hdxm)
      (fun y => f y - f x) (hfcont.measurable.sub measurable_const) H hHn
      (fun y _ => by rw [norm_sub_rev]; exact hH y x)).2
  have hNx' : |∫ y in B, K (x' - y) * (f y - f x')| ≤ Q * H * (2 * δ) ^ α :=
    (near_piece hn α hα₀ i j M hM hb x' B hBm (2 * δ) (by linarith) (hBball x' hdx'm)
      (fun y => f y - f x') (hfcont.measurable.sub measurable_const) H hHn
      (fun y _ => by rw [norm_sub_rev]; exact hH y x')).2
  have hgE : ∀ y ∈ B \ closedBall x' (δ / 2), |f x - f x'| ≤ (2 * H) * ‖x' - y‖ ^ α := by
    intro y hy
    have hy2 : δ / 2 < ‖x' - y‖ := by
      have := hy.2
      rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at this
      linarith
    have hd : δ ^ α ≤ 2 * ‖x' - y‖ ^ α := by
      calc δ ^ α ≤ (2 * ‖x' - y‖) ^ α := Real.rpow_le_rpow hδ.le (by linarith) hα₀.le
        _ = 2 ^ α * ‖x' - y‖ ^ α := Real.mul_rpow (by norm_num) (norm_nonneg _)
        _ ≤ 2 * ‖x' - y‖ ^ α :=
          mul_le_mul_of_nonneg_right h2α (Real.rpow_nonneg (norm_nonneg _) _)
    calc |f x - f x'| ≤ H * δ ^ α := hH x x'
      _ ≤ H * (2 * ‖x' - y‖ ^ α) := mul_le_mul_of_nonneg_left hd hHn
      _ = (2 * H) * ‖x' - y‖ ^ α := by ring
  have hEt : |∫ y in B \ closedBall x' (δ / 2), K (x' - y) * (f x - f x')| ≤
      Q * (2 * H) * (2 * δ) ^ α :=
    (near_piece hn α hα₀ i j M hM hb x' (B \ closedBall x' (δ / 2))
      (hBm.diff measurableSet_closedBall) (2 * δ) (by linarith)
      (diff_subset.trans (hBball x' hdx'm)) (fun _ => f x - f x') measurable_const (2 * H)
      (by positivity) hgE).2
  -- Assembly.
  have hEq : (∫ y in ball x R, K (x - y) * (f y - f x)) -
      (∫ y in ball x' R, K (x' - y) * (f y - f x')) =
      ((∫ y in B, K (x - y) * (f y - f x)) - (∫ y in B, K (x' - y) * (f y - f x'))) +
        (∫ y in E, (K (x - y) - K (x' - y)) * (f y - f x)) +
        ∫ y in B \ closedBall x' (δ / 2), K (x' - y) * (f x - f x') := by
    rw [kx, kx', he, ← hGdiff, integral_mul_const]
    ring
  rw [hEq]
  have hQH : 0 ≤ Q * H := mul_nonneg hQ hHn
  have hNx2 : Q * H * (2 * δ) ^ α ≤ Q * H * (2 * t) := mul_le_mul_of_nonneg_left h2δ hQH
  have hEt2 : Q * (2 * H) * (2 * δ) ^ α ≤ Q * (2 * H) * (2 * t) :=
    mul_le_mul_of_nonneg_left h2δ (by positivity)
  have t1 := abs_add_le ((∫ y in B, K (x - y) * (f y - f x)) - (∫ y in B, K (x' - y) * (f y - f x')) +
    (∫ y in E, (K (x - y) - K (x' - y)) * (f y - f x)))
    (∫ y in B \ closedBall x' (δ / 2), K (x' - y) * (f x - f x'))
  have t2 := abs_add_le ((∫ y in B, K (x - y) * (f y - f x)) - (∫ y in B, K (x' - y) * (f y - f x')))
    (∫ y in E, (K (x - y) - K (x' - y)) * (f y - f x))
  have t3 := abs_sub (∫ y in B, K (x - y) * (f y - f x)) (∫ y in B, K (x' - y) * (f y - f x'))
  calc _ ≤ Q * H * (2 * t) + Q * H * (2 * t) + Afar * H * t + Q * (2 * H) * (2 * t) := by
        linarith
    _ = (8 * Q + Afar) * (H * t) := by ring
    _ ≤ A * (H * t) := by
        apply mul_le_mul_of_nonneg_right _ hHt
        dsimp [A]; linarith [Anear.coe_nonneg]
    _ = A * H * t := by ring

end
