-- Prove2me | solution 1 for GlobalTheory.CubeFrame.cube_eq_on_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:28:39.764512+00:00
-- url     : https://prove2.me/submissions/81a9b5a7-43a1-4d5c-a4fd-2461b2cded39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsGlobalFrameOfLocal
import Theorems.Thm_GlobalTheory_CubeFrame_exists_glue
import Theorems.Thm_GlobalTheory_CubeFrame_differentiableOn_prod_zpow
import Theorems.Thm_GlobalTheory_CubeFrame_differentiableOn_div
import Theorems.Thm_GlobalTheory_CubeFrame_isOpen_cubeChart
import Theorems.Thm_GlobalTheory_SCV_eqOn_of_eventuallyEq


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
    (hc0 : ∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0)
    (hT : ∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))})
    (hTc : ∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) →
      T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) *
        T j' x)
    {r : ℝ} {fr : ι → E → ℂ} {κ : ℂ} (hr : 0 < r)
    (hfd : ∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r))
    (hf0 : ∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0)
    (hfc : ∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)
    (hev : ∀ᶠ x in 𝓝 (0 : Fin 3 → E), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) :
    ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ Metric.ball (0 : E) r) →
      T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card)) := by
  set U : Set (Fin 3 → E) := {x | ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ Metric.ball (0 : E) r}
    with hU
  have hUo : IsOpen U := isOpen_cubeChart (p := fun x => x) continuous_id fun _ => Metric.isOpen_ball
  have hUc : Convex ℝ U := by
    intro x hx y hy a b ha hb hab I
    have := convex_ball (0 : E) r (hx I) (hy I) ha hb hab
    simpa [Finset.sum_add_distrib, Finset.smul_sum] using this
  have hU0 : (0 : Fin 3 → E) ∈ U := fun I => by simpa using hr
  have hcov' : ∀ x : Fin 3 → E, ∃ j : Finset (Fin 3) → ι,
      x ∈ {x : Fin 3 → E | ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)} := fun x => by
    choose j hj using fun I : Finset (Fin 3) => hcov (∑ a ∈ I, x a)
    exact ⟨j, hj⟩
  have hne : ∀ (j : Finset (Fin 3) → ι) x, x ∈ U →
      (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card)) ≠ 0 :=
    fun j x hx hj => Finset.prod_ne_zero_iff.mpr fun I _ => zpow_ne_zero _ (hf0 _ _ (hj I) (hx I))
  obtain ⟨G, hGd, hG⟩ := exists_glue (U := U)
    (A := fun j : Finset (Fin 3) → ι =>
      {x : Fin 3 → E | ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)})
    (F := fun j x => T j x /
      ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card)))
    (fun j => isOpen_cubeChart (p := fun x => x) continuous_id fun I => hW _) hcov'
    (fun j => by
      refine differentiableOn_div ((hT j).mono Set.inter_subset_right) ?_
        fun x hx => hne j x hx.1 hx.2
      refine differentiableOn_prod_zpow _ (f := fun I (x : Fin 3 → E) => fr (j I) (∑ a ∈ I, x a)) _
        (fun I _ => ?_) fun I _ x hx => hf0 _ _ (hx.2 I) (hx.1 I)
      exact (hfd (j I)).comp (by fun_prop) fun x hx => ⟨hx.2 I, hx.1 I⟩)
    (fun j k x hx hj hk => by
      have h1 : ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card)) =
          (∏ I : Finset (Fin 3), c (j I) (k I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) *
          ∏ I : Finset (Fin 3), fr (k I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card)) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun I _ => ?_
        rw [hfc _ _ _ (hj I) (hk I) (hx I), mul_zpow]
      have h2 : ∏ I : Finset (Fin 3), c (j I) (k I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))
          ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun I _ => zpow_ne_zero _ (hc0 _ _ _ (hj I) (hk I))
      rw [hTc j k x hj hk, h1, mul_div_mul_left _ _ h2])
  have hGκ : Set.EqOn G (fun _ => κ) U := by
    refine SCV.eqOn_of_eventuallyEq hUo hUc.isPreconnected hGd (differentiableOn_const κ) hU0 ?_
    filter_upwards [hev, hUo.mem_nhds hU0] with x hx hxU
    obtain ⟨j, hj⟩ := hcov' x
    rw [hG j x hxU hj, hx j hj, mul_div_cancel_right₀ _ (hne j x hxU hj)]
  intro j x hj hx
  have h1 := hGκ hx
  rw [hG j x hx hj] at h1
  exact (div_eq_iff (hne j x hx hj)).mp h1
end GlobalTheory.CubeFrame
