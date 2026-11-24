-- Prove2me | solution 1 for GlobalTheory.CubeFrame.exists_double
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:20:51.9488+00:00
-- url     : https://prove2.me/submissions/8c0f21df-c4dc-4b14-bf40-c84d8e9ba567

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsGlobalFrameOfLocal
import Theorems.Thm_GlobalTheory_CubeFrame_exists_glue
import Theorems.Thm_GlobalTheory_CubeFrame_differentiableOn_prod_zpow
import Theorems.Thm_GlobalTheory_CubeFrame_differentiableOn_div
import Theorems.Thm_GlobalTheory_CubeFrame_isOpen_cubeChart
import Theorems.Thm_GlobalTheory_CubeFrame_differentiable_halfPoint
import Theorems.Thm_GlobalTheory_CubeFrame_sum_halfPoint
import Theorems.Thm_GlobalTheory_CubeFrame_norm_sum_halfPoint_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.CubeFrame
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {ι : Type} {W : ι → Set E} {c : ι → ι → E → ℂ}
  {T : (Finset (Fin 3) → ι) → (Fin 3 → E) → ℂ}
namespace GlobalTheory.CubeFrame
theorem _root_.solution (hW : ∀ i, IsOpen (W i)) (hcov : ∀ z, ∃ i, z ∈ W i)
    (hcd : ∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j))
    (hc0 : ∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0)
    (hcc : ∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z)
    (hT : ∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))})
    (hT0 : ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0)
    (hTc : ∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) →
      T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) *
        T j' x)
    {r : ℝ} {fr : ι → E → ℂ} {κ : ℂ} (hr : 0 < r)
    (hfd : ∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r))
    (hf0 : ∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0)
    (hfc : ∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)
    (hall : ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ Metric.ball (0 : E) r) →
      T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) :
    ∃ fr' : ι → E → ℂ, (∀ i, DifferentiableOn ℂ (fr' i) (W i ∩ Metric.ball 0 (2 * r))) ∧
      (∀ i z, z ∈ W i → z ∈ Metric.ball 0 (2 * r) → fr' i z ≠ 0) ∧
      (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 (2 * r) → fr' i z = c i j z * fr' j z) ∧
      ∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr' i z = fr i z := by
  set D : Finset (Fin 3) := {0, 1} with hD
  set S : Finset (Finset (Fin 3)) := Finset.univ.erase D with hS
  have hκ : κ ≠ 0 := by
    obtain ⟨i, hi⟩ := hcov 0
    have h1 : ∀ I : Finset (Fin 3), ∑ a ∈ I, (0 : Fin 3 → E) a ∈ W ((fun _ => i) I) :=
      fun I => by simpa using hi
    have h2 := hT0 _ _ h1
    rw [hall _ _ h1 fun I => by simpa using hr] at h2
    exact left_ne_zero_of_mul h2
  have hcov' : ∀ w : E, ∃ j : Finset (Fin 3) → ι,
      w ∈ {w : E | ∀ I : Finset (Fin 3), ∑ a ∈ I, halfPoint w a ∈ W (j I)} := fun w => by
    choose j hj using fun I : Finset (Fin 3) => hcov (∑ a ∈ I, halfPoint w a)
    exact ⟨j, hj⟩
  have hball : ∀ w ∈ Metric.ball (0 : E) (2 * r), ∀ I ∈ S,
      ∑ a ∈ I, halfPoint w a ∈ Metric.ball (0 : E) r := fun w hw I hI => by
    rw [mem_ball_zero_iff] at hw ⊢
    have := norm_sum_halfPoint_le w (Finset.ne_of_mem_erase hI)
    linarith
  have hjD : ∀ (j : Finset (Fin 3) → ι) (w : E),
      (∀ I : Finset (Fin 3), ∑ a ∈ I, halfPoint w a ∈ W (j I)) → w ∈ W (j D) := fun j w hj => by
    have := hj D
    rwa [sum_halfPoint] at this
  have hsplit : ∀ (f : Finset (Fin 3) → E → ℂ) (w : E),
      ∏ I : Finset (Fin 3), f I (∑ a ∈ I, halfPoint w a) ^ ((-1 : ℤ) ^ (3 - I.card)) =
      (f D w)⁻¹ * ∏ I ∈ S, f I (∑ a ∈ I, halfPoint w a) ^ ((-1 : ℤ) ^ (3 - I.card)) := by
    intro f w
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ D), sum_halfPoint]
    have : D.card = 2 := rfl
    simp [this, hS]
  have hne : ∀ (j : Finset (Fin 3) → ι), ∀ w ∈ Metric.ball (0 : E) (2 * r),
      (∀ I : Finset (Fin 3), ∑ a ∈ I, halfPoint w a ∈ W (j I)) →
      ∏ I ∈ S, fr (j I) (∑ a ∈ I, halfPoint w a) ^ ((-1 : ℤ) ^ (3 - I.card)) ≠ 0 :=
    fun j w hw hj => Finset.prod_ne_zero_iff.mpr fun I hI =>
      zpow_ne_zero _ (hf0 _ _ (hj I) (hball w hw I hI))
  have hglue := fun i : ι => exists_glue (U := W i ∩ Metric.ball 0 (2 * r))
    (A := fun j : Finset (Fin 3) → ι =>
      {w : E | ∀ I : Finset (Fin 3), ∑ a ∈ I, halfPoint w a ∈ W (j I)})
    (F := fun j w => c i (j D) w * (κ *
      (∏ I ∈ S, fr (j I) (∑ a ∈ I, halfPoint w a) ^ ((-1 : ℤ) ^ (3 - I.card))) /
        T j (halfPoint w)))
    (fun j => isOpen_cubeChart differentiable_halfPoint.continuous fun I => hW _) hcov'
    (fun j => by
      have hp := differentiable_halfPoint (E := E)
      refine DifferentiableOn.mul ((hcd i (j D)).mono fun w hw => ⟨hw.1.1, hjD j w hw.2⟩)
        (differentiableOn_div (DifferentiableOn.const_mul ?_ κ) ?_ fun w hw => hT0 _ _ hw.2)
      · refine differentiableOn_prod_zpow _ (f := fun I w => fr (j I) (∑ a ∈ I, halfPoint w a)) _
          (fun I hI => ?_) fun I hI w hw => hf0 _ _ (hw.2 I) (hball w hw.1.2 I hI)
        exact (hfd (j I)).comp (by fun_prop) fun w hw => ⟨hw.2 I, hball w hw.1.2 I hI⟩
      · exact (hT j).comp hp.differentiableOn fun w hw => hw.2)
    (fun j k w hw hj hk => by
      have h1 : ∏ I ∈ S, fr (j I) (∑ a ∈ I, halfPoint w a) ^ ((-1 : ℤ) ^ (3 - I.card)) =
          (∏ I ∈ S, c (j I) (k I) (∑ a ∈ I, halfPoint w a) ^ ((-1 : ℤ) ^ (3 - I.card))) *
          ∏ I ∈ S, fr (k I) (∑ a ∈ I, halfPoint w a) ^ ((-1 : ℤ) ^ (3 - I.card)) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun I hI => ?_
        rw [hfc _ _ _ (hj I) (hk I) (hball w hw.2 I hI), mul_zpow]
      have h2 : ∏ I ∈ S, c (j I) (k I) (∑ a ∈ I, halfPoint w a) ^ ((-1 : ℤ) ^ (3 - I.card))
          ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun I _ => zpow_ne_zero _ (hc0 _ _ _ (hj I) (hk I))
      have h3 := hc0 _ _ _ (hjD j w hj) (hjD k w hk)
      have h4 := hT0 _ _ hk
      rw [hTc j k _ hj hk, h1, hsplit (fun I => c (j I) (k I)),
        ← hcc i (j D) (k D) w hw.1 (hjD j w hj) (hjD k w hk)]
      field_simp)
  choose fr' hd hfr' using hglue
  refine ⟨fr', hd, fun i z hi hz => ?_, fun i i' z hi hi' hz => ?_, fun i z hi hz => ?_⟩
  · obtain ⟨j, hj⟩ := hcov' z
    rw [hfr' i j z ⟨hi, hz⟩ hj]
    exact mul_ne_zero (hc0 _ _ _ hi (hjD j z hj))
      (div_ne_zero (mul_ne_zero hκ (hne j z hz hj)) (hT0 _ _ hj))
  · obtain ⟨j, hj⟩ := hcov' z
    rw [hfr' i j z ⟨hi, hz⟩ hj, hfr' i' j z ⟨hi', hz⟩ hj, ← mul_assoc,
      hcc i i' _ z hi hi' (hjD j z hj)]
  · obtain ⟨j, hj⟩ := hcov' z
    have hz2 : z ∈ Metric.ball (0 : E) (2 * r) := Metric.ball_subset_ball (by linarith) hz
    have hb : ∀ I : Finset (Fin 3), ∑ a ∈ I, halfPoint z a ∈ Metric.ball (0 : E) r := fun I => by
      by_cases hI : I = D
      · rw [hI, sum_halfPoint]; exact hz
      · exact hball z hz2 I (Finset.mem_erase.mpr ⟨hI, Finset.mem_univ I⟩)
    have h1 := hne j z hz2 hj
    have h2 := hf0 _ _ (hjD j z hj) hz
    rw [hfr' i j z ⟨hi, hz2⟩ hj, hall j _ hj hb, hsplit (fun I => fr (j I)),
      hfc i _ z hi (hjD j z hj) hz]
    field_simp
end GlobalTheory.CubeFrame
