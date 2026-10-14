-- Prove2me | solution 1 for ModernOnlineLearning.Dynamic.theorem_14_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:13:15.752634+00:00
-- url     : https://prove2.me/submissions/3a536eb5-b028-43db-b219-34d9cf1dac4e

import Mathlib
import Definitions.Def_ModernOnlineLearning_Dynamic_Defs

namespace RRAux_Dyn142
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma slope_tendsto (f : E → ℝ) (a v : E) (hf : DifferentiableAt ℝ f a) :
    Tendsto (fun s : ℝ => s⁻¹ * (f (a + s • v) - f a)) (𝓝[>] 0) (𝓝 (fderiv ℝ f a v)) := by
  have h1 : HasDerivAt (fun s : ℝ => a + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add a
  have h3 : HasFDerivAt f (fderiv ℝ f a) ((fun s : ℝ => a + s • v) 0) := by
    simpa using hf.hasFDerivAt
  have h2 := (h3.comp_hasDerivAt (0:ℝ) h1).tendsto_slope_zero_right
  simpa [Function.comp_def] using h2

lemma first_order (ψ : E → ℝ) (V : Set E) (hV : Convex ℝ V) (g : E →L[ℝ] ℝ) (c : ℝ)
    (_hc : 0 ≤ c) (y xn u : E) (hxn : xn ∈ V) (hu : u ∈ V) (hdn : DifferentiableAt ℝ ψ xn)
    (hmin : ∀ z ∈ V, g xn + c * BeckTeboulleMD.EMDA.bregman ψ xn y ≤
      g z + c * BeckTeboulleMD.EMDA.bregman ψ z y) :
    0 ≤ g (u - xn) + c * (fderiv ℝ ψ xn (u - xn) - fderiv ℝ ψ y (u - xn)) := by
  have hT := slope_tendsto ψ xn (u - xn) hdn
  have hT2 : Tendsto (fun s : ℝ => g (u - xn) + c * (s⁻¹ * (ψ (xn + s • (u - xn)) - ψ xn))
      - c * fderiv ℝ ψ y (u - xn)) (𝓝[>] 0)
      (𝓝 (g (u - xn) + c * fderiv ℝ ψ xn (u - xn) - c * fderiv ℝ ψ y (u - xn))) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul hT)).sub tendsto_const_nhds)
  have key : 0 ≤ g (u - xn) + c * fderiv ℝ ψ xn (u - xn) - c * fderiv ℝ ψ y (u - xn) := by
    refine ge_of_tendsto hT2 ?_
    have hIoo : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hIoo] with s hs
    have hzV : xn + s • (u - xn) ∈ V := hV.add_smul_sub_mem hxn hu ⟨hs.1.le, hs.2.le⟩
    have h := hmin _ hzV
    unfold BeckTeboulleMD.EMDA.bregman at h
    have e1 : xn + s • (u - xn) - y = (xn - y) + s • (u - xn) := by abel
    rw [e1, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    have hs0 : 0 < s := hs.1
    -- h : g xn + c*(ψ xn - ψ y - Dy(xn-y)) ≤ g xn + s*g(u-xn) + c*(ψ z - ψ y - (Dy(xn-y) + s*Dy(u-xn)))
    have h' : 0 ≤ s * (g (u - xn) + c * (s⁻¹ * (ψ (xn + s • (u - xn)) - ψ xn))
        - c * fderiv ℝ ψ y (u - xn)) := by
      have : s * (g (u - xn) + c * (s⁻¹ * (ψ (xn + s • (u - xn)) - ψ xn))
          - c * fderiv ℝ ψ y (u - xn))
          = s * g (u - xn) + c * (ψ (xn + s • (u - xn)) - ψ xn)
            - c * (s * fderiv ℝ ψ y (u - xn)) := by
        field_simp
      rw [this]; nlinarith
    exact (mul_nonneg_iff_of_pos_left hs0).mp h'
  linarith

lemma strong_bregman (ψ : E → ℝ) (C : Set E) (lam : ℝ) (hst : StrongConvexOn C lam ψ)
    (x y : E) (hx : x ∈ C) (hy : y ∈ C) (hdy : DifferentiableAt ℝ ψ y) :
    lam / 2 * ‖x - y‖ ^ 2 ≤ BeckTeboulleMD.EMDA.bregman ψ x y := by
  unfold BeckTeboulleMD.EMDA.bregman
  have hT := slope_tendsto ψ y (x - y) hdy
  have hK : Tendsto (fun s : ℝ => (1 - s) * (lam / 2 * ‖x - y‖ ^ 2)) (𝓝[>] 0)
      (𝓝 (lam / 2 * ‖x - y‖ ^ 2)) := by
    have : Tendsto (fun s : ℝ => (1 - s) * (lam / 2 * ‖x - y‖ ^ 2)) (𝓝 0)
        (𝓝 ((1 - 0) * (lam / 2 * ‖x - y‖ ^ 2))) :=
      ((continuous_const.sub continuous_id).mul continuous_const).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hsum := hT.add hK
  have key : fderiv ℝ ψ y (x - y) + lam / 2 * ‖x - y‖ ^ 2 ≤ ψ x - ψ y := by
    refine le_of_tendsto hsum ?_
    have hIoo : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hIoo] with s hs
    have hs0 : 0 < s := hs.1
    have h := hst.2 hx hy hs.1.le (sub_nonneg.mpr hs.2.le) (by ring)
    have e : s • x + (1 - s) • y = y + s • (x - y) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [e, smul_eq_mul, smul_eq_mul] at h
    -- h : ψ (y + s(x-y)) ≤ s ψ x + (1-s) ψ y - s(1-s) * (lam/2 * ‖x-y‖^2)
    have : s⁻¹ * (ψ (y + s • (x - y)) - ψ y) ≤ ψ x - ψ y - (1 - s) * (lam / 2 * ‖x - y‖ ^ 2) := by
      rw [inv_mul_le_iff₀ hs0]
      linear_combination h
    linarith
  linarith

lemma young (a d η lam : ℝ) (hη : 0 < η) (hlam : 0 < lam) :
    a * d ≤ η / (2 * lam) * a ^ 2 + 1 / η * (lam / 2 * d ^ 2) := by
  have h : η / (2 * lam) * a ^ 2 + 1 / η * (lam / 2 * d ^ 2) - a * d
      = (η * a - lam * d) ^ 2 / (2 * η * lam) := by
    field_simp; ring
  have : 0 ≤ (η * a - lam * d) ^ 2 / (2 * η * lam) := by positivity
  linarith

lemma one_step (ψ : E → ℝ) (V C : Set E) (g : E →L[ℝ] ℝ) (η lam : ℝ) (hη : 0 < η)
    (hlam : 0 < lam) (hV : Convex ℝ V) (hst : StrongConvexOn C lam ψ)
    (xt xn u : E) (hxt : xt ∈ C) (hxn : xn ∈ C) (hxnV : xn ∈ V) (hu : u ∈ V)
    (hdt : DifferentiableAt ℝ ψ xt) (hdn : DifferentiableAt ℝ ψ xn)
    (hmin : ∀ z ∈ V, g xn + (1 / η) * BeckTeboulleMD.EMDA.bregman ψ xn xt ≤
      g z + (1 / η) * BeckTeboulleMD.EMDA.bregman ψ z xt) :
    g (xt - u) ≤ (BeckTeboulleMD.EMDA.bregman ψ u xt - BeckTeboulleMD.EMDA.bregman ψ u xn) / η
      + η / (2 * lam) * ‖g‖ ^ 2 := by
  have hp : 0 < 1 / η := by positivity
  have fo := first_order ψ V hV g (1 / η) hp.le xt xn u hxnV hu hdn hmin
  have three : BeckTeboulleMD.EMDA.bregman ψ u xt - BeckTeboulleMD.EMDA.bregman ψ u xn
      - BeckTeboulleMD.EMDA.bregman ψ xn xt
      = fderiv ℝ ψ xn (u - xn) - fderiv ℝ ψ xt (u - xn) := by
    unfold BeckTeboulleMD.EMDA.bregman
    have : fderiv ℝ ψ xt (u - xt) = fderiv ℝ ψ xt (u - xn) + fderiv ℝ ψ xt (xn - xt) := by
      rw [← map_add]; congr 1; abel
    rw [this]; ring
  have sc := strong_bregman ψ C lam hst xn xt hxn hxt hdt
  have gn : g (xt - xn) ≤ ‖g‖ * ‖xn - xt‖ := by
    rw [← norm_neg (xn - xt), neg_sub]
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ g.le_opNorm (xt - xn))
  have split : g (xt - u) = g (xt - xn) - g (u - xn) := by
    rw [← map_sub]; congr 1; abel
  have yo := young ‖g‖ ‖xn - xt‖ η lam hη hlam
  have sc' : 1 / η * (lam / 2 * ‖xn - xt‖ ^ 2) ≤ 1 / η * BeckTeboulleMD.EMDA.bregman ψ xn xt :=
    mul_le_mul_of_nonneg_left sc hp.le
  have hdiv : (BeckTeboulleMD.EMDA.bregman ψ u xt - BeckTeboulleMD.EMDA.bregman ψ u xn) / η
      = 1 / η * (BeckTeboulleMD.EMDA.bregman ψ u xt - BeckTeboulleMD.EMDA.bregman ψ u xn) := by
    ring
  rw [hdiv, split]
  have fo' : -g (u - xn) ≤ 1 / η * (BeckTeboulleMD.EMDA.bregman ψ u xt
      - BeckTeboulleMD.EMDA.bregman ψ u xn - BeckTeboulleMD.EMDA.bregman ψ xn xt) := by
    rw [three]; linarith
  have e2 : 1 / η * (BeckTeboulleMD.EMDA.bregman ψ u xt
      - BeckTeboulleMD.EMDA.bregman ψ u xn - BeckTeboulleMD.EMDA.bregman ψ xn xt)
      = 1 / η * (BeckTeboulleMD.EMDA.bregman ψ u xt - BeckTeboulleMD.EMDA.bregman ψ u xn)
        - 1 / η * BeckTeboulleMD.EMDA.bregman ψ xn xt := by ring
  rw [e2] at fo'
  linarith

lemma telescope (ψ : E → ℝ) (x u : ℕ → E) (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.Icc 1 T, (BeckTeboulleMD.EMDA.bregman ψ (u t) (x t)
      - BeckTeboulleMD.EMDA.bregman ψ (u t) (x (t + 1)))
    = BeckTeboulleMD.EMDA.bregman ψ (u T) (x 1) - BeckTeboulleMD.EMDA.bregman ψ (u T) (x (T + 1))
      + ∑ t ∈ Finset.Icc 2 T, (fderiv ℝ ψ (x 1) - fderiv ℝ ψ (x t)) (u t - u (t - 1)) := by
  induction T, hT using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
    simp only [Nat.add_sub_cancel, BeckTeboulleMD.EMDA.bregman, ContinuousLinearMap.sub_apply,
      map_sub]
    ring

lemma shift_bound (ψ : E → ℝ) (x u : ℕ → E) (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.Icc 2 T, (fderiv ℝ ψ (x 1) - fderiv ℝ ψ (x t)) (u t - u (t - 1))
      ≤ ModernOnlineLearning.Dynamic.maxGradientShift ψ x T hT *
        ModernOnlineLearning.Dynamic.pathLength u T := by
  unfold ModernOnlineLearning.Dynamic.pathLength
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  have ht' : t ∈ Finset.Icc 1 T := by
    rw [Finset.mem_Icc] at ht ⊢; omega
  have hQ : ‖fderiv ℝ ψ (x t) - fderiv ℝ ψ (x 1)‖ ≤
      ModernOnlineLearning.Dynamic.maxGradientShift ψ x T hT := by
    unfold ModernOnlineLearning.Dynamic.maxGradientShift
    exact Finset.le_max' ((Finset.Icc 1 T).image (fun t => ‖fderiv ℝ ψ (x t) - fderiv ℝ ψ (x 1)‖)) _
      (Finset.mem_image.mpr ⟨t, ht', rfl⟩)
  calc (fderiv ℝ ψ (x 1) - fderiv ℝ ψ (x t)) (u t - u (t - 1))
      ≤ ‖(fderiv ℝ ψ (x 1) - fderiv ℝ ψ (x t)) (u t - u (t - 1))‖ := le_abs_self _
    _ ≤ ‖fderiv ℝ ψ (x 1) - fderiv ℝ ψ (x t)‖ * ‖u t - u (t - 1)‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ ψ (x t) - fderiv ℝ ψ (x 1)‖ * ‖u t - u (t - 1)‖ := by rw [norm_sub_rev]
    _ ≤ _ := mul_le_mul_of_nonneg_right hQ (norm_nonneg _)

end RRAux_Dyn142

open ModernOnlineLearning.Dynamic in
theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X V : Set E) (ψ : E → ℝ) (η : ℝ) (ℓ : ℕ → E → ℝ)
    (x u : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) (T : ℕ) (lam : ℝ)
    (hT : 1 ≤ T) (hη : 0 < η) (hlam : 0 < lam)
    (hVsub : V ⊆ X) (hVne : V.Nonempty) (hVclosed : IsClosed V)
    (hVconv : Convex ℝ V) (hXconv : Convex ℝ X)
    (hψclosed : ClosedRegularizerOn X ψ)
    (hψstrict : StrictConvexOn ℝ X ψ)
    (hψdiff : DifferentiableOn ℝ ψ (interior X))
    (hψstrong : StrongConvexOn (V ∩ interior X) lam ψ)
    (hrun : IsOMDRun X V ψ (fun _ => η) ℓ x g T)
    (hu : ∀ t ∈ Finset.Icc 1 T, u t ∈ V) :
    dynamicRegret ℓ x u T ≤
      (BeckTeboulleMD.EMDA.bregman ψ (u T) (x 1) +
        maxGradientShift ψ x T hT * pathLength u T) / η +
      (η / (2 * lam)) * (∑ t ∈ Finset.Icc 1 T, ‖g t‖ ^ 2) -
      BeckTeboulleMD.EMDA.bregman ψ (u T) (x (T + 1)) / η := by
  obtain ⟨_, hstep⟩ := hrun
  have hper : ∀ t ∈ Finset.Icc 1 T, ℓ t (x t) - ℓ t (u t) ≤
      (BeckTeboulleMD.EMDA.bregman ψ (u t) (x t)
        - BeckTeboulleMD.EMDA.bregman ψ (u t) (x (t + 1))) / η
        + η / (2 * lam) * ‖g t‖ ^ 2 := by
    intro t ht
    obtain ⟨_, hxt, hxn, _, hsub, hmin⟩ := hstep t ht
    have hut := hu t ht
    have hdt : DifferentiableAt ℝ ψ (x t) :=
      hψdiff.differentiableAt (isOpen_interior.mem_nhds hxt.2)
    have hdn : DifferentiableAt ℝ ψ (x (t + 1)) :=
      hψdiff.differentiableAt (isOpen_interior.mem_nhds hxn.2)
    have h1 := hsub (u t) hut
    have h2 := RRAux_Dyn142.one_step ψ V (V ∩ interior X) (g t) η lam hη hlam hVconv hψstrong
      (x t) (x (t + 1)) (u t) hxt hxn hxn.1 hut hdt hdn hmin
    have h3 : g t (x t - u t) = - g t (u t - x t) := by rw [← map_neg, neg_sub]
    linarith
  unfold dynamicRegret
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum,
    RRAux_Dyn142.telescope ψ x u T hT] at hsum
  have hb := RRAux_Dyn142.shift_bound ψ x u T hT
  have hdiv : (BeckTeboulleMD.EMDA.bregman ψ (u T) (x 1)
        - BeckTeboulleMD.EMDA.bregman ψ (u T) (x (T + 1))
        + ∑ t ∈ Finset.Icc 2 T, (fderiv ℝ ψ (x 1) - fderiv ℝ ψ (x t)) (u t - u (t - 1))) / η
      ≤ (BeckTeboulleMD.EMDA.bregman ψ (u T) (x 1) +
        maxGradientShift ψ x T hT * pathLength u T) / η
        - BeckTeboulleMD.EMDA.bregman ψ (u T) (x (T + 1)) / η := by
    rw [div_sub_div_same]
    exact div_le_div_of_nonneg_right (by linarith) hη.le
  linarith

#print axioms solution
