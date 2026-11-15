-- Prove2me | solution 1 for LG2021.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-14T17:11:46.950847+00:00
-- url     : https://prove2.me/submissions/f611356e-f20c-4235-ba3e-077e5d030bac

import Mathlib
import Definitions.Def_LG2021_CanonicalBandit
import Definitions.Def_LG2021_RegretRate
import Definitions.Def_LG2021_Policy
import Theorems.Thm_LG2021_theorem_2

set_option autoImplicit false
set_option maxHeartbeats 2000000

section

namespace BilateralProfitMHR.CorollaryTransport

open MeasureTheory
open scoped ENNReal

















section Geometry

variable {X Y Ω : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]





private theorem mapQuery_isOn (f : Y → X) (hf : Measurable f) (A : QueryAlg Y Ω)
    {K : Set X} {R : Set Y} (hA : A.IsOn R) (hfK : Set.MapsTo f R K) :
    (mapQuery f hf A).IsOn K := by
  intro τ ω y
  exact hfK (hA τ ω y)

private theorem pullKernel_measurable (f : Y → X) (hf : Measurable f)
    (ν : ObsKernel X) (hν : ν.IsMeasurable) : (pullKernel f ν).IsMeasurable := by
  intro τ
  change Measurable (fun w : (Fin τ → Y) × (Fin τ → ℝ) × Y =>
    ν τ (fun i => f (w.1 i)) w.2.1 (f w.2.2))
  exact (hν τ).comp (show Measurable (fun w : (Fin τ → Y) × (Fin τ → ℝ) × Y =>
    ((fun i => f (w.1 i)), w.2.1, f w.2.2)) from by fun_prop)



private theorem cumLoss_mapQuery (f : Y → X) (hf : Measurable f) (A : QueryAlg Y Ω)
    (ν : ObsKernel X) (g : X → ℝ≥0∞) (ω : Ω) (m τ : ℕ) (y : Fin τ → ℝ) :
    cumLoss (mapQuery f hf A) ν g ω m τ y =
      cumLoss A (pullKernel f ν) (g ∘ f) ω m τ y := by
  induction m generalizing τ with
  | zero => rfl
  | succ m ih =>
      simp only [cumLoss, mapQuery, Function.comp_apply]
      congr 1
      apply lintegral_congr
      intro z
      exact ih (τ + 1) (Fin.snoc y z)

private theorem expectedCumLoss_mapQuery (f : Y → X) (hf : Measurable f) (A : QueryAlg Y Ω)
    (P : Measure Ω) (ν : ObsKernel X) (g : X → ℝ≥0∞) (n : ℕ) :
    expectedCumLoss (mapQuery f hf A) P ν g n =
      expectedCumLoss A P (pullKernel f ν) (g ∘ f) n := by
  apply lintegral_congr
  intro ω
  exact cumLoss_mapQuery f hf A ν g ω n 0 Fin.elim0

end Geometry



section Observations

variable {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]











end Observations

end BilateralProfitMHR.CorollaryTransport
end

section

/-!
The global extension needed only in the analysis of the bandit policy.
The infimal-convolution construction follows the existing real Lipschitz
extension proof in Mathlib; compact convexity additionally preserves convexity.
The infimal-convolution formulation supplies the global extension used in the formal proof.
-/

noncomputable section

namespace LG2021

open Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



private theorem convexLipschitzExtension_attains {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (C : ℝ≥0) (f : E → ℝ) (hf : ContinuousOn f K) (x : E) :
    ∃ y ∈ K, convexLipschitzExtension K C f x = f y + (C : ℝ) * ‖x - y‖ ∧
      ∀ z ∈ K, convexLipschitzExtension K C f x ≤ f z + (C : ℝ) * ‖x - z‖ := by
  have hc : ContinuousOn (fun y => f y + (C : ℝ) * ‖x - y‖) K :=
    hf.add (continuousOn_const.mul (continuous_const.sub continuous_id).norm.continuousOn)
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hne hc
  have hleast : IsLeast ((fun z => f z + (C : ℝ) * ‖x - z‖) '' K)
      (f y + (C : ℝ) * ‖x - y‖) := by
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro t ⟨z, hz, rfl⟩
    exact hmin hz
  have he : convexLipschitzExtension K C f x = f y + (C : ℝ) * ‖x - y‖ := hleast.csInf_eq
  exact ⟨y, hy, he, fun z hz => he.trans_le (hmin hz)⟩

private theorem convexLipschitzExtension_agrees {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (C : ℝ≥0) (f : E → ℝ) (hf : LipschitzOnWith C f K) :
    EqOn (convexLipschitzExtension K C f) f K := by
  intro x hx
  obtain ⟨y, hy, he, hbound⟩ := convexLipschitzExtension_attains hK hne C f hf.continuousOn x
  apply le_antisymm
  · simpa using hbound x hx
  · rw [he]
    simpa only [dist_eq_norm] using hf.le_add_mul hx hy

private theorem convexLipschitzExtension_lipschitz {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (C : ℝ≥0) (f : E → ℝ) (hf : ContinuousOn f K) :
    LipschitzWith C (convexLipschitzExtension K C f) := by
  apply LipschitzWith.of_le_add_mul C
  intro x y
  obtain ⟨u, hu, hy, _⟩ := convexLipschitzExtension_attains hK hne C f hf y
  obtain ⟨_, _, _, hx⟩ := convexLipschitzExtension_attains hK hne C f hf x
  have htri : ‖x - u‖ ≤ ‖x - y‖ + ‖y - u‖ := norm_sub_le_norm_sub_add_norm_sub x y u
  calc
    convexLipschitzExtension K C f x ≤ f u + (C : ℝ) * ‖x - u‖ := hx u hu
    _ ≤ f u + (C : ℝ) * (‖x - y‖ + ‖y - u‖) := by gcongr
    _ = convexLipschitzExtension K C f y + (C : ℝ) * dist x y := by
      rw [hy, dist_eq_norm]
      ring

private theorem convexLipschitzExtension_convex {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (C : ℝ≥0) (f : E → ℝ) (hf : ContinuousOn f K) (hfc : ConvexOn ℝ K f) :
    ConvexOn ℝ Set.univ (convexLipschitzExtension K C f) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  obtain ⟨u, hu, hxu, _⟩ := convexLipschitzExtension_attains hK hne C f hf x
  obtain ⟨v, hv, hyv, _⟩ := convexLipschitzExtension_attains hK hne C f hf y
  obtain ⟨_, _, _, hmix⟩ := convexLipschitzExtension_attains hK hne C f hf (a • x + b • y)
  have hz : a • u + b • v ∈ K := hfc.1 hu hv ha hb hab
  have hcost := hmix (a • u + b • v) hz
  have hconv := hfc.2 hu hv ha hb hab
  have hnorm : ‖a • x + b • y - (a • u + b • v)‖ ≤
      a * ‖x - u‖ + b * ‖y - v‖ := by
    have he : a • x + b • y - (a • u + b • v) = a • (x - u) + b • (y - v) := by module
    rw [he]
    exact (norm_add_le _ _).trans_eq (by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb])
  have hmult := mul_le_mul_of_nonneg_left hnorm C.property
  simp only [smul_eq_mul] at hconv ⊢
  rw [hxu, hyv]
  nlinarith

private theorem convexLipschitzExtension_nonneg {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (C : ℝ≥0) (f : E → ℝ) (hf : ContinuousOn f K) (hfn : ∀ y ∈ K, 0 ≤ f y) (x : E) :
    0 ≤ convexLipschitzExtension K C f x := by
  obtain ⟨y, hy, he, _⟩ := convexLipschitzExtension_attains hK hne C f hf x
  rw [he]
  exact add_nonneg (hfn y hy) (mul_nonneg C.property (norm_nonneg _))

end LG2021
end
end

section

noncomputable section

namespace LG2021

open Concentration

private theorem sourceLog_lower {n : ℕ} (hn : 2 ≤ n) {D : ℝ} (hD : 2 ≤ D) :
    1 ≤ Real.log ((n : ℝ) * D) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hND : (4 : ℝ) ≤ (n : ℝ) * D := by nlinarith
  apply (Real.le_log_iff_exp_le (by positivity : 0 < (n : ℝ) * D)).2
  linarith [Real.exp_one_lt_three]



private theorem sharpRate_nonneg {d n : ℕ} (hn : 2 ≤ n) {D : ℝ} (hD : 2 ≤ D) :
    0 ≤ sharpRate d D n := by
  unfold sharpRate
  have ht := sourceLog_lower hn hD
  positivity

private theorem sharpRate_lower {d n : ℕ} (hn : 2 ≤ n) {D : ℝ} (hD : 2 ≤ D) :
    (d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n ≤ sharpRate d D n := by
  have ht := sourceLog_lower hn hD
  have hst := Real.one_le_sqrt.2 ht
  have hf : 1 ≤ Real.log ((n : ℝ) * D) * Real.sqrt (Real.log ((n : ℝ) * D)) := by
    nlinarith
  have hm : (1 : ℝ) ≤ max 1 (Real.sqrt (Real.log ((n : ℝ) * D)) / (d : ℝ)) := le_max_left _ _
  unfold sharpRate
  calc
    _ = ((d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n) * 1 * 1 := by ring
    _ ≤ _ := by gcongr

private theorem one_le_sharpRate {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {D : ℝ} (hD : 2 ≤ D) : 1 ≤ sharpRate d D n := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hsd := Real.one_le_sqrt.2 hdR
  have hsn := Real.one_le_sqrt.2 hnR
  have hp : (1 : ℝ) ≤ (d : ℝ) ^ 4 := one_le_pow₀ hdR
  apply le_trans _ (sharpRate_lower hn hD)
  calc
    (1 : ℝ) = 1 * 1 * 1 := by norm_num
    _ ≤ (d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n := by gcongr





private theorem sharpRate_eq_max {d n : ℕ} (hd : 0 < d) {D : ℝ}
    (ht : 0 ≤ Real.log ((n : ℝ) * D)) :
    sharpRate d D n =
      max ((d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n *
          (Real.log ((n : ℝ) * D) * Real.sqrt (Real.log ((n : ℝ) * D))))
        ((d : ℝ) ^ 3 * Real.sqrt d * Real.sqrt n *
          Real.log ((n : ℝ) * D) ^ 2) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsq := Real.sq_sqrt ht
  unfold sharpRate
  rw [mul_max_of_nonneg _ _ (by positivity)]
  simp only [mul_one]
  congr 1
  field_simp
  linear_combination Real.sqrt n * Real.log ((n : ℝ) * D) * hsq



private theorem sourceLog_horizon_le {n : ℕ} (hn : 2 ≤ n) {D : ℝ} (hD : 2 ≤ D) :
    Real.log (n : ℝ) ≤ Real.log ((n : ℝ) * D) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact Real.log_le_log hnpos (by nlinarith)





private theorem sharpRate_erosion_le {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {D : ℝ} (hD : 2 ≤ D) :
    sharpRate d ((n : ℝ) * D) n ≤ 4 * sharpRate d D n := by
  let t := Real.log ((n : ℝ) * D)
  let t' := Real.log ((n : ℝ) * ((n : ℝ) * D))
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hD' : 2 ≤ (n : ℝ) * D := by nlinarith
  have ht : 1 ≤ t := sourceLog_lower hn hD
  have ht' : 1 ≤ t' := sourceLog_lower hn hD'
  have ht'eq : t' = Real.log n + t := by
    exact Real.log_mul hnpos.ne' (by positivity : (n : ℝ) * D ≠ 0)
  have ht'le : t' ≤ 2 * t := by
    rw [ht'eq]
    linarith [sourceLog_horizon_le hn hD]
  have hs : Real.sqrt t' ≤ 2 * Real.sqrt t := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 2 * Real.sqrt t)).2
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ t)]
  rw [sharpRate_eq_max hd (by dsimp [t'] at ht'; linarith),
    sharpRate_eq_max hd (by dsimp [t] at ht; linarith)]
  change max ((d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n * (t' * Real.sqrt t'))
      ((d : ℝ) ^ 3 * Real.sqrt d * Real.sqrt n * t' ^ 2) ≤
    4 * max ((d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n * (t * Real.sqrt t))
      ((d : ℝ) ^ 3 * Real.sqrt d * Real.sqrt n * t ^ 2)
  apply max_le
  · calc
      _ ≤ (d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n * ((2 * t) * (2 * Real.sqrt t)) := by
        gcongr
      _ = 4 * ((d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n * (t * Real.sqrt t)) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · calc
      _ ≤ (d : ℝ) ^ 3 * Real.sqrt d * Real.sqrt n * (2 * t) ^ 2 := by
        gcongr
      _ = 4 * ((d : ℝ) ^ 3 * Real.sqrt d * Real.sqrt n * t ^ 2) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _







end LG2021
end
end

section

namespace BilateralProfitMHR.CorollaryTransport

open MeasureTheory
open scoped ENNReal
























private theorem sInf_loss_image {X Y : Type} (f : Y → X) {R : Set Y} {K : Set X}
    (himage : f '' R = K) (L : X → ℝ) :
    sInf ((L ∘ f) '' R) = sInf (L '' K) := by
  change sInf ((fun x => L (f x)) '' R) = _
  rw [← Set.image_image L f R, himage]

private theorem expectedRegret_mapQuery {X Y Ω : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Ω] (f : Y → X) (hf : Measurable f)
    {R : Set Y} {K : Set X} (himage : f '' R = K) (L : X → ℝ)
    (A : QueryAlg Y Ω) (P : Measure Ω) (ν : ObsKernel X) (n : ℕ) :
    expectedCumLoss (mapQuery f hf A) P ν
      (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n =
    expectedCumLoss A P (pullKernel f ν)
      (fun x => ENNReal.ofReal ((L ∘ f) x - sInf ((L ∘ f) '' R))) n := by
  rw [expectedCumLoss_mapQuery, sInf_loss_image f himage L]
  rfl

private theorem pullKernel_unitNoiseCond {X Y : Type} (f : Y → X) (ν : ObsKernel X)
    {K : Set X} {R : Set Y} (hfK : Set.MapsTo f R K) (L : X → ℝ)
    (hν : UnitNoiseCond K L ν) : UnitNoiseCond R (L ∘ f) (pullKernel f ν) := by
  intro τ xs ys x hxs hx
  exact hν τ (fun i => f (xs i)) ys (f x) (fun i => hfK (hxs i)) (hfK hx)

end BilateralProfitMHR.CorollaryTransport
end

section

/-!
The known-body erosion used in Appendix F of Lattimore and György (2021).
The interior Lipschitz proof adapts Mathlib's convex secant argument, using
the loss range [0,1] to obtain the exact constant. The loss and its extension
are analysis objects; the eroded body uses only the known body and scale.
-/

noncomputable section
namespace LG2021

open Set Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def innerOffset (K : Set E) (ε : ℝ) : Set E :=
  {x | ∀ v : E, ‖v‖ ≤ ε → x + v ∈ K}

private theorem innerOffset_subset {K : Set E} {ε : ℝ} (hε : 0 ≤ ε) :
    innerOffset K ε ⊆ K := by
  intro x hx
  simpa using hx 0 (by simpa using hε)

private theorem innerOffset_closed {K : Set E} (hK : IsClosed K) (ε : ℝ) :
    IsClosed (innerOffset K ε) := by
  have he : innerOffset K ε = ⋂ (v : E) (_ : ‖v‖ ≤ ε),
      (fun x : E => x + v) ⁻¹' K := by
    ext x
    simp only [innerOffset, mem_setOf_eq, mem_iInter, mem_preimage]
  rw [he]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    hK.preimage (continuous_id.add continuous_const)

private theorem innerOffset_compact {K : Set E} (hK : IsCompact K) {ε : ℝ} (hε : 0 ≤ ε) :
    IsCompact (innerOffset K ε) :=
  hK.of_isClosed_subset (innerOffset_closed hK.isClosed ε) (innerOffset_subset hε)

private theorem innerOffset_convex {K : Set E} (hK : Convex ℝ K) (ε : ℝ) :
    Convex ℝ (innerOffset K ε) := by
  intro x hx y hy a b ha hb hab v hv
  have h := hK (hx v hv) (hy v hv) ha hb hab
  have he : a • (x + v) + b • (y + v) = (a • x + b • y) + v := by
    rw [smul_add, smul_add]
    calc
      a • x + a • v + (b • y + b • v) =
          (a • x + b • y) + (a + b) • v := by rw [add_smul]; abel
      _ = _ := by rw [hab, one_smul]
  rwa [he] at h

private theorem closedBall_subset_innerOffset {K : Set E} {a ε : ℝ}
    (hball : closedBall (0 : E) a ⊆ K) :
    closedBall (0 : E) (a - ε) ⊆ innerOffset K ε := by
  intro x hx v hv
  apply hball
  rw [mem_closedBall_zero_iff] at hx ⊢
  exact (norm_add_le x v).trans (by linarith)

private theorem homothety_mem_innerOffset {K : Set E} (hK : Convex ℝ K)
    (hball : closedBall (0 : E) 1 ⊆ K) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {x : E} (hx : x ∈ K) : (1 - ε) • x ∈ innerOffset K ε := by
  intro v hv
  have hv' : ε⁻¹ • v ∈ K := by
    apply hball
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hε.le)]
    exact (inv_mul_le_one₀ hε).2 hv
  have h := hK hx hv' (show 0 ≤ 1 - ε by linarith) hε.le (by ring)
  simpa only [smul_smul, mul_inv_cancel₀ hε.ne', one_smul] using h

/-- An adaptation of Mathlib's convex secant estimate to an inner parallel body. -/
private theorem convexOn_lipschitz_innerOffset {K : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ K f) (hrange : ∀ x ∈ K, f x ∈ Icc (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) :
    LipschitzOnWith (1 / ε).toNNReal f (innerOffset K ε) := by
  apply LipschitzOnWith.of_le_add_mul' (1 / ε)
  intro x hx y hy
  obtain rfl | hxy := eq_or_ne x y
  · simp
  have hx' : x ∈ K := innerOffset_subset hε.le hx
  have hy' : y ∈ K := innerOffset_subset hε.le hy
  let z := x + (ε / ‖x - y‖) • (x - y)
  replace hxy : 0 < ‖x - y‖ := by rwa [norm_sub_pos_iff]
  have hz : z ∈ K := hx _ (by
    simp [norm_smul, abs_of_nonneg, hε.le, hxy.ne'])
  let a := ε / (ε + ‖x - y‖)
  let b := ‖x - y‖ / (ε + ‖x - y‖)
  have hab : a + b = 1 := by simp [field, a, b]
  have hxyz : x = a • y + b • z := by
    calc
      x = a • x + b • x := by rw [Convex.combo_self hab]
      _ = a • y + b • z := by simp [z, a, b, smul_smul, hxy.ne', smul_sub]; abel
  have hsec : ε * (f x - f y) ≤ ‖x - y‖ * (f z - f x) := by
    have h := hf.2 hy' hz (by positivity) (by positivity) hab
    simp only [← hxyz, smul_eq_mul, a, b] at h
    field_simp at h
    linear_combination h
  have hbounded : ‖x - y‖ * (f z - f x) ≤ ‖x - y‖ := by
    have hzx : f z - f x ≤ 1 := by linarith [(hrange z hz).2, (hrange x hx').1]
    simpa using mul_le_mul_of_nonneg_left hzx (norm_nonneg (x - y))
  have hbound : f x - f y ≤ ‖x - y‖ / ε := (le_div_iff₀' hε).2 (hsec.trans hbounded)
  rw [dist_eq_norm]
  simp only [div_eq_mul_inv, one_mul] at hbound ⊢
  rw [mul_comm ε⁻¹]
  linarith

private def scaledInnerBody (K : Set E) (s : ℝ) : Set E :=
  (fun x : E => s • x) '' innerOffset K s⁻¹

private theorem scaledInnerBody_compact {K : Set E} (hK : IsCompact K) {s : ℝ} (hs : 0 ≤ s) :
    IsCompact (scaledInnerBody K s) :=
  (innerOffset_compact hK (inv_nonneg.mpr hs)).image (continuous_const.smul continuous_id)

private theorem scaledInnerBody_convex {K : Set E} (hK : Convex ℝ K) (s : ℝ) :
    Convex ℝ (scaledInnerBody K s) := by
  exact (innerOffset_convex hK s⁻¹).smul s

private theorem scaledInnerBody_unscale {K : Set E} {s : ℝ} (hs : 0 < s)
    {x : E} (hx : x ∈ scaledInnerBody K s) : s⁻¹ • x ∈ innerOffset K s⁻¹ := by
  obtain ⟨y, hy, rfl⟩ := hx
  simpa [smul_smul, hs.ne'] using hy

private theorem scaledInnerBody_mapsTo {K : Set E} {s : ℝ} (hs : 0 < s) :
    MapsTo (fun x : E => s⁻¹ • x) (scaledInnerBody K s) K :=
  fun _ hx => innerOffset_subset (inv_nonneg.mpr hs.le) (scaledInnerBody_unscale hs hx)

private theorem scaledInnerBody_inner_ball {K : Set E} {s : ℝ} (hs : 0 < s)
    (hball : closedBall (0 : E) 1 ⊆ K) :
    closedBall (0 : E) (s - 1) ⊆ scaledInnerBody K s := by
  intro x hx
  refine ⟨s⁻¹ • x, ?_, by simp [smul_smul, hs.ne']⟩
  apply closedBall_subset_innerOffset hball
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hs.le)]
  rw [mem_closedBall_zero_iff] at hx
  have h := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hs.le)
  calc
    s⁻¹ * ‖x‖ ≤ s⁻¹ * (s - 1) := h
    _ = 1 - s⁻¹ := by field_simp



private theorem scaledLoss_lipschitz {K : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ K f) (hrange : ∀ x ∈ K, f x ∈ Icc (0 : ℝ) 1)
    {s : ℝ} (hs : 0 < s) :
    LipschitzOnWith 1 (fun x : E => f (s⁻¹ • x)) (scaledInnerBody K s) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h := (convexOn_lipschitz_innerOffset hf hrange (inv_pos.mpr hs)).dist_le_mul
    (s⁻¹ • x) (scaledInnerBody_unscale hs hx) (s⁻¹ • y) (scaledInnerBody_unscale hs hy)
  have hcoef : ((1 / s⁻¹).toNNReal : ℝ) = s := by simp [hs.le]
  rw [hcoef] at h
  simp only [dist_eq_norm] at h ⊢
  rw [← smul_sub, norm_smul] at h
  simpa [Real.norm_eq_abs, abs_of_nonneg hs.le, abs_of_nonneg (inv_nonneg.mpr hs.le),
    ← mul_assoc, hs.ne'] using h

private theorem scaledLoss_convex {K : Set E} {f : E → ℝ} (hf : ConvexOn ℝ K f)
    {s : ℝ} (hs : 0 < s) :
    ConvexOn ℝ (scaledInnerBody K s) (fun x : E => f (s⁻¹ • x)) := by
  refine ⟨scaledInnerBody_convex hf.1 s, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hf.2 (scaledInnerBody_mapsTo hs hx) (scaledInnerBody_mapsTo hs hy) ha hb hab
  simpa only [smul_add, smul_comm (s⁻¹) a, smul_comm (s⁻¹) b] using h

private theorem scaledLoss_range {K : Set E} {f : E → ℝ}
    (hrange : ∀ x ∈ K, f x ∈ Icc (0 : ℝ) 1) {s : ℝ} (hs : 0 < s) :
    ∀ x ∈ scaledInnerBody K s, f (s⁻¹ • x) ∈ Icc (0 : ℝ) 1 :=
  fun x hx => hrange _ (scaledInnerBody_mapsTo hs hx)

private theorem erosion_comparator {K : Set E} {f : E → ℝ} (hf : ConvexOn ℝ K f)
    (hball : closedBall (0 : E) 1 ⊆ K) (hrange : ∀ x ∈ K, f x ∈ Icc (0 : ℝ) 1)
    {s : ℝ} (hs : 1 ≤ s) {x : E} (hx : x ∈ K) :
    ∃ y ∈ scaledInnerBody K s, f (s⁻¹ • y) ≤ f x + s⁻¹ := by
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hε : 0 < s⁻¹ := inv_pos.mpr hspos
  have hε1 : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  refine ⟨s • ((1 - s⁻¹) • x), ⟨_, homothety_mem_innerOffset hf.1 hball hε hε1 hx, rfl⟩, ?_⟩
  have hzero : (0 : E) ∈ K := hball (by simp)
  have h := hf.2 hx hzero (sub_nonneg.mpr hε1) hε.le (by ring)
  simp only [smul_zero, add_zero, smul_eq_mul] at h
  simp only [smul_smul, ← mul_assoc, inv_mul_cancel₀ hspos.ne', one_mul]
  nlinarith [(hrange 0 hzero).2, (hrange x hx).1]

/-- The analysis loss is globally convex and Lipschitz and equals the observed
loss on the known eroded domain. Its definition is not an input to the policy. -/
private theorem eroded_analysis_loss {K : Set E} (hK : IsCompact K)
    (hball : closedBall (0 : E) 1 ⊆ K) {f : E → ℝ}
    (hf : ConvexOn ℝ K f) (hrange : ∀ x ∈ K, f x ∈ Icc (0 : ℝ) 1)
    {s : ℝ} (hs : 1 ≤ s) :
    ∃ F : E → ℝ, ConvexOn ℝ univ F ∧ LipschitzWith 1 F ∧
      (∀ x, 0 ≤ F x) ∧
      EqOn F (fun x => f (s⁻¹ • x)) (scaledInnerBody K s) ∧
      (∀ x ∈ scaledInnerBody K s, F x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ K, ∃ y ∈ scaledInnerBody K s, F y ≤ f x + s⁻¹) := by
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hcompact := scaledInnerBody_compact hK hspos.le
  have hzero : (0 : E) ∈ scaledInnerBody K s :=
    scaledInnerBody_inner_ball hspos hball (by simpa using sub_nonneg.mpr hs)
  have hne : (scaledInnerBody K s).Nonempty := ⟨0, hzero⟩
  let g : E → ℝ := fun x => f (s⁻¹ • x)
  have hglip : LipschitzOnWith 1 g (scaledInnerBody K s) := scaledLoss_lipschitz hf hrange hspos
  have hgconv : ConvexOn ℝ (scaledInnerBody K s) g := scaledLoss_convex hf hspos
  have hgrange : ∀ x ∈ scaledInnerBody K s, g x ∈ Icc (0 : ℝ) 1 :=
    scaledLoss_range hrange hspos
  let F := convexLipschitzExtension (scaledInnerBody K s) 1 g
  have heq : EqOn F g (scaledInnerBody K s) :=
    convexLipschitzExtension_agrees hcompact hne 1 g hglip
  refine ⟨F, convexLipschitzExtension_convex hcompact hne 1 g hglip.continuousOn hgconv,
    convexLipschitzExtension_lipschitz hcompact hne 1 g hglip.continuousOn,
    convexLipschitzExtension_nonneg hcompact hne 1 g hglip.continuousOn
      (fun x hx => (hgrange x hx).1), heq, ?_, ?_⟩
  · intro x hx
    rw [heq hx]
    exact hgrange x hx
  · intro x hx
    obtain ⟨y, hy, hbound⟩ := erosion_comparator hf hball hrange hs hx
    exact ⟨y, hy, (heq hy).trans_le hbound⟩

end LG2021
end
end

section

noncomputable section

namespace LG2021

private theorem sharpRate_mono_diameter {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {D E : ℝ} (hD : 2 ≤ D) (hE : 2 ≤ E) (hDE : D ≤ E) :
    sharpRate d D n ≤ sharpRate d E n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have htD := sourceLog_lower hn hD
  have htE := sourceLog_lower hn hE
  have hlogs : Real.log ((n : ℝ) * D) ≤ Real.log ((n : ℝ) * E) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hDE hnpos.le)
  rw [sharpRate_eq_max hd (by linarith : 0 ≤ Real.log ((n : ℝ) * D)),
    sharpRate_eq_max hd (by linarith : 0 ≤ Real.log ((n : ℝ) * E))]
  apply max_le_max <;> gcongr








end LG2021
end
end

section

noncomputable section
namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal

/-- A per-round additive cost comparison survives the exact adaptive nested
kernel semantics, including kernels depending on every previous observation. -/
private theorem cumLoss_le_add_of_pointwise {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (ν : ObsKernel X) {K : Set X} (hA : A.IsOn K)
    (hν : ∀ τ xs ys x, (∀ i, xs i ∈ K) → x ∈ K → IsProbabilityMeasure (ν τ xs ys x))
    (g h : X → ℝ≥0∞) (B : ℝ≥0∞) (hgh : ∀ x ∈ K, g x ≤ h x + B)
    (ω : Ω) (m τ : ℕ) (y : Fin τ → ℝ) :
    cumLoss A ν g ω m τ y ≤ cumLoss A ν h ω m τ y + m * B := by
  induction m generalizing τ with
  | zero => simp [cumLoss]
  | succ m ih =>
      letI := hν τ (A.pastQueries ω y) y (A.query τ ω y)
        (fun i => hA i ω _) (hA τ ω y)
      change g (A.query τ ω y) + (∫⁻ z, cumLoss A ν g ω m (τ + 1) (Fin.snoc y z)
        ∂ν τ (A.pastQueries ω y) y (A.query τ ω y)) ≤ _
      calc
        _ ≤ (h (A.query τ ω y) + B) +
            ∫⁻ z, (cumLoss A ν h ω m (τ + 1) (Fin.snoc y z) + m * B)
              ∂ν τ (A.pastQueries ω y) y (A.query τ ω y) :=
          add_le_add (hgh _ (hA τ ω y)) (lintegral_mono fun z => ih (τ + 1) (Fin.snoc y z))
        _ = cumLoss A ν h ω (m + 1) τ y + (m + 1 : ℕ) * B := by
          rw [lintegral_add_right _ measurable_const]
          simp [cumLoss, Nat.cast_add, add_mul, add_assoc, add_comm, add_left_comm]

private theorem expectedCumLoss_le_add_of_pointwise {X Ω : Type} [MeasurableSpace X]
    [MeasurableSpace Ω] (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ObsKernel X) {K : Set X} (hA : A.IsOn K)
    (hν : ∀ τ xs ys x, (∀ i, xs i ∈ K) → x ∈ K → IsProbabilityMeasure (ν τ xs ys x))
    (g h : X → ℝ≥0∞) (B : ℝ≥0∞) (hgh : ∀ x ∈ K, g x ≤ h x + B) (n : ℕ) :
    expectedCumLoss A P ν g n ≤ expectedCumLoss A P ν h n + n * B := by
  calc
    _ ≤ ∫⁻ ω, (cumLoss A ν h ω n 0 Fin.elim0 + n * B) ∂P :=
      lintegral_mono fun ω => cumLoss_le_add_of_pointwise A ν hA hν g h B hgh ω n 0 Fin.elim0
    _ = _ := by rw [lintegral_add_right _ measurable_const]; simp [expectedCumLoss]

private theorem pullKernel_unitNoiseCond_of_eqOn {X Y : Type} (p : Y → X) (ν : ObsKernel X)
    {K : Set X} {R : Set Y} (hp : MapsTo p R K) (L : X → ℝ) (F : Y → ℝ)
    (hF : EqOn F (L ∘ p) R) (hν : UnitNoiseCond K L ν) :
    UnitNoiseCond R F (pullKernel p ν) := by
  intro τ xs ys x hxs hx
  have h := pullKernel_unitNoiseCond p ν hp L hν τ xs ys x hxs hx
  simpa only [← hF hx] using h

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]





end LG2021
end
end

section

/-!
Transport of the explicit universal dimension bound through Lipschitz extension
and the known-body erosion. The comparator is an infimum, so the convex loss
need not be continuous at the boundary of its domain.
-/

noncomputable section
namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal











section Erosion

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The erosion comparator uses only the infimum of the original loss. Thus no
boundary continuity or existence of a minimizing point is required. -/
private theorem eroded_infimum_le {K : Set E} (hK : IsCompact K)
    (hball : closedBall (0 : E) 1 ⊆ K) {f : E → ℝ}
    (hf : ConvexOn ℝ K f) (hrange : ∀ x ∈ K, f x ∈ Icc (0 : ℝ) 1)
    {s : ℝ} (hs : 1 ≤ s) {F : E → ℝ}
    (hF : ContinuousOn F (scaledInnerBody K s))
    (heq : EqOn F (fun x => f (s⁻¹ • x)) (scaledInnerBody K s)) :
    sInf (F '' scaledInnerBody K s) ≤ sInf (f '' K) + s⁻¹ := by
  have hne : (f '' K).Nonempty := ⟨f 0, 0, hball (by simp), rfl⟩
  have hbounded : BddBelow (F '' scaledInnerBody K s) :=
    ((scaledInnerBody_compact hK (by linarith)).image_of_continuousOn hF).bddBelow
  have hbound : sInf (F '' scaledInnerBody K s) - s⁻¹ ≤ sInf (f '' K) := by
    apply le_csInf hne
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hcomp⟩ := erosion_comparator hf hball hrange hs hx
    have hmin := csInf_le hbounded (mem_image_of_mem F hy)
    rw [heq hy] at hmin
    linarith
  linarith

private theorem expectedRegret_erosion_infimum {Ω : Type} [MeasurableSpace Ω]
    {K : Set E} (hK : IsCompact K) (hball : closedBall (0 : E) 1 ⊆ K)
    {f : E → ℝ} (hf : ConvexOn ℝ K f)
    (hrange : ∀ x ∈ K, f x ∈ Icc (0 : ℝ) 1)
    {n : ℕ} (hn : 1 ≤ n) {F : E → ℝ}
    (hF : ContinuousOn F (scaledInnerBody K (n : ℝ)))
    (heq : EqOn F (fun x => f ((n : ℝ)⁻¹ • x)) (scaledInnerBody K (n : ℝ)))
    (A : QueryAlg E Ω) (hA : A.IsOn (scaledInnerBody K (n : ℝ)))
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : ObsKernel E)
    (hν : UnitNoiseCond K f ν) :
    expectedCumLoss (mapQuery (fun x : E => (n : ℝ)⁻¹ • x) (by fun_prop) A) P ν
      (fun x => ENNReal.ofReal (f x - sInf (f '' K))) n ≤
    expectedCumLoss A P (pullKernel (fun x : E => (n : ℝ)⁻¹ • x) ν)
      (fun x => ENNReal.ofReal (F x - sInf (F '' scaledInnerBody K (n : ℝ)))) n + 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hmin := eroded_infimum_le hK hball hf hrange hnR hF heq
  rw [expectedCumLoss_mapQuery]
  have hbound := expectedCumLoss_le_add_of_pointwise A P
    (pullKernel (fun x : E => (n : ℝ)⁻¹ • x) ν) hA
    (fun τ xs ys x hxs hx =>
      (pullKernel_unitNoiseCond (fun x : E => (n : ℝ)⁻¹ • x) ν
        (scaledInnerBody_mapsTo hnpos) f hν τ xs ys x hxs hx).1)
    ((fun x => ENNReal.ofReal (f x - sInf (f '' K))) ∘ (fun x : E => (n : ℝ)⁻¹ • x))
    (fun x => ENNReal.ofReal (F x - sInf (F '' scaledInnerBody K (n : ℝ))))
    (ENNReal.ofReal (n : ℝ)⁻¹) (fun x hx => by
      simp only [Function.comp_apply]
      calc
        _ ≤ ENNReal.ofReal (F x - sInf (F '' scaledInnerBody K (n : ℝ)) + (n : ℝ)⁻¹) := by
          apply ENNReal.ofReal_le_ofReal
          rw [heq hx]
          linarith
        _ ≤ _ := ENNReal.ofReal_add_le) n
  have hunit : (n : ℝ≥0∞) * ENNReal.ofReal (n : ℝ)⁻¹ = 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hnpos.le,
      mul_inv_cancel₀ hnpos.ne', ENNReal.ofReal_one]
  simpa only [hunit] using hbound

end Erosion

private theorem scaledInnerBody_diameter {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {s D : ℝ} (hs : 0 < s)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    ∀ x ∈ scaledInnerBody K s, ∀ y ∈ scaledInnerBody K s, dist x y ≤ s * D := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg hs.le]
  exact mul_le_mul_of_nonneg_left
    (hdiam x (innerOffset_subset (inv_nonneg.mpr hs.le) hx)
      y (innerOffset_subset (inv_nonneg.mpr hs.le) hy)) hs.le

/-- Erosion changes the known diameter bound from `D` to `n * D` and adds at
most one unit of expected regret. The original convex loss can be discontinuous. -/
private theorem sharp_eroded_bandit_raw {C : ℝ} (hcanonical : SharpCanonicalBandit C)
    {d : ℕ} (hd : 0 < d) {n : ℕ} (hn : 2 ≤ n) {D : ℝ} (hD : 2 ≤ D)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K) (hcv : Convex ℝ K)
    (hinner : closedBall 0 1 ⊆ K) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
        ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
          ConvexOn ℝ K L → (∀ x ∈ K, L x ∈ Icc 0 1) →
          ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
            UnitNoiseCond K L ν →
              expectedCumLoss A P ν
                (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                  ENNReal.ofReal (C * sharpRate d ((n : ℝ) * D) n) + 1 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  let S := scaledInnerBody K (n : ℝ)
  have hS : IsCompact S := scaledInnerBody_compact hK hnpos.le
  have hSc : Convex ℝ S := scaledInnerBody_convex hcv _
  have hSi : closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ S :=
    (closedBall_subset_closedBall (by linarith : (1 : ℝ) ≤ (n : ℝ) - 1)).trans
      (scaledInnerBody_inner_ball hnpos hinner)
  have hSd := scaledInnerBody_diameter hnpos hdiam
  have hscale : 2 ≤ (n : ℝ) * D := by nlinarith
  obtain ⟨Ω, mΩ, P, hP, A, hA, hregret⟩ :=
    hcanonical d hd n hn ((n : ℝ) * D) hscale S hS hSc hSi hSd
  letI := mΩ
  letI := hP
  let p : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun x => (n : ℝ)⁻¹ • x
  have hp : Measurable p := by fun_prop
  have hpK : MapsTo p S K := scaledInnerBody_mapsTo hnpos
  refine ⟨Ω, mΩ, P, hP, mapQuery p hp A, mapQuery_isOn p hp A hA hpK, ?_⟩
  intro L hLv hLr ν hνm hν
  obtain ⟨F, hFc, hFl, hFn, hFeq, hFr, _⟩ :=
    eroded_analysis_loss hK hinner hLv hLr (by linarith : (1 : ℝ) ≤ n)
  have hnoise := pullKernel_unitNoiseCond_of_eqOn p ν hpK L F hFeq hν
  have hmeas := pullKernel_measurable p hp ν hνm
  have hb := hregret F hFc hFl hFn hFr (pullKernel p ν) hmeas hnoise
  have he := expectedRegret_erosion_infimum hK hinner hLv hLr (by omega : 1 ≤ n)
    hFl.continuous.continuousOn hFeq A hA P ν hν
  exact he.trans (add_le_add hb le_rfl)

end LG2021
end
end

section

/-!
The explicit source rate for arbitrary locations of the contained unit ball.
The loss comparator is its infimum on the compact action set; whenever the
minimum is attained this equals the source's minimum comparator.
-/

noncomputable section
namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal

/-- The universal-constant statement for bounded convex losses on a body
containing a unit ball, with its actual diameter in the explicit rate. -/
private def SharpConvexBandit (C : ℝ) : Prop :=
  ∀ d : ℕ, 0 < d → ∀ n : ℕ, 2 ≤ n →
    ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
      (∃ a, closedBall a 1 ⊆ K) →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
        ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
          ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
            ConvexOn ℝ K L → (∀ x ∈ K, L x ∈ Icc 0 1) →
            ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
              UnitNoiseCond K L ν →
                expectedCumLoss A P ν
                  (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                    ENNReal.ofReal (C * sharpRate d (Metric.diam K) n)

/-- The corresponding source statement when the loss is one-Lipschitz on the
known body. The loss and adaptive noise follow the choice of the policy. -/
private def SharpLipschitzBandit (C : ℝ) : Prop :=
  ∀ d : ℕ, 0 < d → ∀ n : ℕ, 2 ≤ n →
    ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
      (∃ a, closedBall a 1 ⊆ K) →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
        ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
          ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
            ConvexOn ℝ K L → LipschitzOnWith 1 L K →
            (∀ x ∈ K, L x ∈ Icc 0 1) →
            ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
              UnitNoiseCond K L ν →
                expectedCumLoss A P ν
                  (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                    ENNReal.ofReal (C * sharpRate d (Metric.diam K) n)

private theorem two_le_diameter_of_unitBall {d : ℕ} (hd : 0 < d)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    {a : EuclideanSpace ℝ (Fin d)} (hinner : closedBall a 1 ⊆ K) :
    2 ≤ Metric.diam K := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hball := Metric.diam_closedBall_eq a (by norm_num : (0 : ℝ) ≤ 1)
  have hm := Metric.diam_mono hinner hK.isBounded
  simpa only [hball, mul_one] using hm

private theorem sharp_eroded_bandit_of_canonical {C : ℝ} (hC : 0 ≤ C)
    (hcanonical : SharpCanonicalBandit C) {d : ℕ} (hd : 0 < d)
    {n : ℕ} (hn : 2 ≤ n) {D : ℝ} (hD : 2 ≤ D)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K) (hcv : Convex ℝ K)
    (hinner : closedBall 0 1 ⊆ K) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
        ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
          ConvexOn ℝ K L → (∀ x ∈ K, L x ∈ Icc 0 1) →
          ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
            UnitNoiseCond K L ν →
              expectedCumLoss A P ν
                (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                  ENNReal.ofReal ((4 * C + 1) * sharpRate d D n) := by
  obtain ⟨Ω, mΩ, P, hP, A, hA, hregret⟩ :=
    sharp_eroded_bandit_raw hcanonical hd hn hD K hK hcv hinner hdiam
  letI := mΩ
  refine ⟨Ω, mΩ, P, hP, A, hA, ?_⟩
  intro L hLv hLr ν hνm hν
  have hscale := sharpRate_erosion_le hd hn hD
  have hone := one_le_sharpRate hd hn hD
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hrate : 0 ≤ sharpRate d ((n : ℝ) * D) n := sharpRate_nonneg hn (by nlinarith)
  have hraw := hregret L hLv hLr ν hνm hν
  calc
    _ ≤ ENNReal.ofReal (C * sharpRate d ((n : ℝ) * D) n) + 1 := hraw
    _ = ENNReal.ofReal (C * sharpRate d ((n : ℝ) * D) n + 1) := by
      rw [ENNReal.ofReal_add (mul_nonneg hC hrate) (by norm_num), ENNReal.ofReal_one]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hmul := mul_le_mul_of_nonneg_left hscale hC
      nlinarith)



/-- Theorem 1 transport with the explicit universal rate. No boundary continuity
of the unknown bounded convex loss is assumed. -/
private theorem theorem_1_of_canonical {C : ℝ} (hC : 0 ≤ C)
    (hcanonical : SharpCanonicalBandit C) {d : ℕ} (hd : 0 < d)
    {n : ℕ} (hn : 2 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K) (hcv : Convex ℝ K)
    (hball : ∃ a, closedBall a 1 ⊆ K) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
        ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
          ConvexOn ℝ K L → (∀ x ∈ K, L x ∈ Icc 0 1) →
          ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
            UnitNoiseCond K L ν →
              expectedCumLoss A P ν
                (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                  ENNReal.ofReal ((4 * C + 1) * sharpRate d (Metric.diam K) n) := by
  obtain ⟨a, ha⟩ := hball
  let R : Set (EuclideanSpace ℝ (Fin d)) := (fun x => a + x) ⁻¹' K
  let f : EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] EuclideanSpace ℝ (Fin d) :=
    (AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin d)) a).toAffineMap
  have hf : Continuous f := by change Continuous (fun x => a + x); fun_prop
  have hR : IsCompact R := (Homeomorph.addLeft a).isCompact_preimage.2 hK
  have hRc : Convex ℝ R := hcv.translate_preimage_right a
  have hRi : closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ R := by
    intro x hx
    apply ha
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hx
  have himage : f '' R = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨x - a, ?_, ?_⟩ <;> simpa [R, f, add_comm a, sub_add_cancel] using hx
  have hmap : MapsTo f R K := fun _ hx => hx
  have hD : 2 ≤ Metric.diam K := two_le_diameter_of_unitBall hd hK ha
  have hRd : ∀ x ∈ R, ∀ y ∈ R, dist x y ≤ Metric.diam K := by
    intro x hx y hy
    have h := Metric.dist_le_diam_of_mem hK.isBounded hx hy
    simpa only [dist_add_left] using h
  obtain ⟨Ω, mΩ, P, hP, A, hA, hregret⟩ :=
    sharp_eroded_bandit_of_canonical hC hcanonical hd hn hD R hR hRc hRi hRd
  letI := mΩ
  refine ⟨Ω, mΩ, P, hP, mapQuery f hf.measurable A,
    mapQuery_isOn f hf.measurable A hA hmap, ?_⟩
  intro L hLv hLr ν hνm hν
  have hcompv : ConvexOn ℝ R (L ∘ f) := (hLv.comp_affineMap f).subset hmap hRc
  have hcompr : ∀ x ∈ R, (L ∘ f) x ∈ Icc (0 : ℝ) 1 := fun x hx => hLr _ (hmap hx)
  have hb := hregret (L ∘ f) hcompv hcompr (pullKernel f ν)
    (pullKernel_measurable f hf.measurable ν hνm) (pullKernel_unitNoiseCond f ν hmap L hν)
  rw [expectedRegret_mapQuery f hf.measurable himage L]
  exact hb

/-- A diameter upper bound may replace the actual diameter in the Lipschitz
source theorem. This provides the interface used by the erosion argument. -/
private theorem sharpCanonicalBandit_of_source_lipschitz {C : ℝ} (hC : 0 ≤ C)
    (hsource : SharpLipschitzBandit C) : SharpCanonicalBandit C := by
  intro d hd n hn D hD K hK hcv hinner hdiam
  obtain ⟨Ω, mΩ, P, hP, A, hA, hregret⟩ :=
    hsource d hd n hn K hK hcv ⟨0, hinner⟩
  letI := mΩ
  refine ⟨Ω, mΩ, P, hP, A, hA, ?_⟩
  intro L hLv hLl _hLn hLr ν hνm hν
  have hlocalv : ConvexOn ℝ K L := hLv.subset (subset_univ K) hcv
  have hb := hregret L hlocalv hLl.lipschitzOnWith hLr ν hνm hν
  have hactual : 2 ≤ Metric.diam K := two_le_diameter_of_unitBall hd hK hinner
  have hupper : Metric.diam K ≤ D :=
    Metric.diam_le_of_forall_dist_le (by linarith) hdiam
  exact hb.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (sharpRate_mono_diameter hd hn hactual hD hupper) hC))

/-- Appendix-F transport, expressed directly as an implication between the two
source theorem statements. -/
private theorem source_theorem_1_of_theorem_2 {C : ℝ} (hC : 0 ≤ C)
    (hsource : SharpLipschitzBandit C) : SharpConvexBandit (4 * C + 1) := by
  intro d hd n hn K hK hcv hball
  exact theorem_1_of_canonical hC (sharpCanonicalBandit_of_source_lipschitz hC hsource)
    hd hn K hK hcv hball

end LG2021
end
end

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric LG2021

theorem solution : ∃ C : ℝ, 0 ≤ C ∧
∀ d : ℕ, 0 < d → ∀ n : ℕ, 2 ≤ n →
    ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
      (∃ a, closedBall a 1 ⊆ K) →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
        ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
          ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
            ConvexOn ℝ K L → (∀ x ∈ K, L x ∈ Icc 0 1) →
            ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
              UnitNoiseCond K L ν →
                expectedCumLoss A P ν
                  (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                    ENNReal.ofReal (C * sharpRate d (Metric.diam K) n) := by
  obtain ⟨C, hC, hsource⟩ := LG2021.theorem_2
  exact ⟨4 * C + 1, by positivity, LG2021.source_theorem_1_of_theorem_2 hC hsource⟩
