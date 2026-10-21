-- Prove2me | solution 1 for ModernOnlineLearning.Dynamic.lemma_6_10
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:26:49.578452+00:00
-- url     : https://prove2.me/submissions/17031fec-35c3-4162-8685-39d59ade10be

import Definitions.Def_ModernOnlineLearning_OMD_Defs
import Definitions.Def_ModernOnlineLearning_Dynamic_Defs
import Theorems.Thm_ModernOnlineLearning_OMD_lemma_6_7

set_option autoImplicit false
open Filter Topology
open ModernOnlineLearning.OMD
open BeckTeboulleMD.EMDA (bregman)
open ModernOnlineLearning.Dynamic (ClosedRegularizerOn)

private lemma convex_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (ψ : E → ℝ) (hc : ConvexOn ℝ X ψ) (x z : E)
    (hx : x ∈ X) (hz : z ∈ X) (hd : DifferentiableAt ℝ ψ x) :
    ψ x + fderiv ℝ ψ x (z - x) ≤ ψ z := by
  let L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x z
  have hline : ConvexOn ℝ (L ⁻¹' X) (ψ ∘ L) := hc.comp_affineMap L
  have hx0 : (0 : ℝ) ∈ L ⁻¹' X := by simpa [L] using hx
  have hz1 : (1 : ℝ) ∈ L ⁻¹' X := by simpa [L] using hz
  have hfd : HasFDerivAt ψ (fderiv ℝ ψ x) (L 0) := by simpa [L] using hd.hasFDerivAt
  have hld : HasDerivAt (ψ ∘ L) (fderiv ℝ ψ x (z - x)) 0 := by
    simpa [L] using hfd.comp_hasDerivAt 0 (AffineMap.hasDerivAt_lineMap (a := x) (b := z) (x := (0 : ℝ)))
  have hbound := hline.le_slope_of_hasDerivAt hx0 hz1 (by norm_num) hld
  have hs : fderiv ℝ ψ x (z - x) ≤ ψ z - ψ x := by
    simpa [slope_def_field, L] using hbound
  linarith

private lemma step_scaled {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (ψ : E → ℝ) (η : ℝ) (hη : 0 < η) (g : E →L[ℝ] ℝ)
    (x y : E) (hx : x ∈ V) (hd : DifferentiableAt ℝ ψ x) :
    IsOMDStep V ψ η g x y ↔ y ∈ V ∧ ∀ z ∈ V,
      η * g y + bregman ψ y x ≤ η * g z + bregman ψ z x := by
  have heq : ∀ z, η * (g z + (1 / η) * bregman ψ z x) = η * g z + bregman ψ z x := by
    intro z
    field_simp
  constructor
  · rintro ⟨_, _, _, hy, hm⟩
    refine ⟨hy, fun z hz => ?_⟩
    have h := mul_le_mul_of_nonneg_left (hm z hz) hη.le
    simpa only [heq] using h
  · rintro ⟨hy, hm⟩
    refine ⟨hη, hx, hd, hy, fun z hz => ?_⟩
    apply (mul_le_mul_iff_right₀ hη).mp
    simpa only [heq] using hm z hz

private lemma strong_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (f : E → ℝ) (lam : ℝ) (hstrong : StrongConvexOn D lam f)
    (y x : E) (hy : y ∈ D) (hx : x ∈ D) (g : E →L[ℝ] ℝ)
    (hg : IsSubgradientOn D f y g) :
    f y + g (x - y) + lam / 2 * ‖y - x‖ ^ 2 ≤ f x := by
  have hsegment : ∀ t : ℝ, 0 < t → t < 1 →
      (1 - t) * (lam / 2 * ‖y - x‖ ^ 2) ≤ f x - f y - g (x - y) := by
    intro t ht ht1
    have ha : 0 ≤ 1 - t := by linarith
    have hab : 1 - t + t = 1 := by ring
    have hv := hstrong.1 hy hx ha ht.le hab
    have hm := hg _ hv
    have hs := hstrong.2 hy hx ha ht.le hab
    simp only [map_sub, map_add, map_smul, smul_eq_mul] at hm hs ⊢
    nlinarith
  have hl : Tendsto (fun t : ℝ => (1 - t) * (lam / 2 * ‖y - x‖ ^ 2))
      (𝓝[>] 0) (𝓝 (lam / 2 * ‖y - x‖ ^ 2)) := by
    have hcont : ContinuousAt (fun t : ℝ => (1 - t) * (lam / 2 * ‖y - x‖ ^ 2)) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hbound : lam / 2 * ‖y - x‖ ^ 2 ≤ f x - f y - g (x - y) := by
    apply le_of_tendsto hl
    filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    exact hsegment t ht ht1
  linarith

private lemma young_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E →L[ℝ] ℝ) (z : E) (lam : ℝ) (hlam : 0 < lam) :
    g z - lam / 2 * ‖z‖ ^ 2 ≤ ‖g‖ ^ 2 / (2 * lam) := by
  have ho : g z ≤ ‖g‖ * ‖z‖ := by
    have h := g.le_opNorm z
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  apply (le_div_iff₀ (show 0 < 2 * lam by positivity)).mpr
  nlinarith [sq_nonneg (‖g‖ - lam * ‖z‖)]

private lemma normal_condition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (hV : Convex ℝ V) (ψ : E → ℝ) (η : ℝ) (g : E →L[ℝ] ℝ)
    (x y u : E) (hstep : IsOMDStep V ψ η g x y) (hu : u ∈ V)
    (hdy : DifferentiableAt ℝ ψ y) :
    0 ≤ η * g (u - y) + fderiv ℝ ψ y (u - y) - fderiv ℝ ψ x (u - y) := by
  let A : E →L[ℝ] ℝ := η • g - fderiv ℝ ψ x
  let c : ℝ := fderiv ℝ ψ x x - ψ x
  let H : E → ℝ := fun z => ψ z + A z + c
  have heq : ∀ z, H z = η * g z + bregman ψ z x := by
    intro z
    simp only [H, A, c, bregman, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, map_sub, smul_eq_mul]
    ring
  have hm := (step_scaled V ψ η hstep.1 g x y hstep.2.1 hstep.2.2.1).mp hstep
  have hmin : IsMinOn H V y := by
    intro z hz
    change H y ≤ H z
    simpa only [heq] using hm.2 z hz
  have hd : HasFDerivAt H (fderiv ℝ ψ y + A) y := by
    exact (hdy.hasFDerivAt.add A.hasFDerivAt).add_const c
  have ht : u - y ∈ posTangentConeAt V y :=
    sub_mem_posTangentConeAt_of_openSegment_subset (hV.openSegment_subset hm.1 hu)
  have hn := hmin.localize.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt ht
  simp only [ContinuousLinearMap.add_apply, A, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at hn
  linarith

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X V : Set E) (ψ : E → ℝ) (η : ℕ → ℝ) (ℓ : ℕ → E → ℝ)
    (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) (T : ℕ) (lam : ℝ)
    (hVsub : V ⊆ X) (hVne : V.Nonempty) (hVclosed : IsClosed V)
    (hVconv : Convex ℝ V) (hXconv : Convex ℝ X)
    (hψclosed : ClosedRegularizerOn X ψ)
    (hψstrict : StrictConvexOn ℝ X ψ)
    (hψdiff : DifferentiableOn ℝ ψ (interior X))
    (hlam : 0 < lam) (hψstrong : StrongConvexOn (V ∩ interior X) lam ψ)
    (hrun : ModernOnlineLearning.Dynamic.IsOMDRun X V ψ η ℓ x g T) :
    ∀ t ∈ Finset.Icc 1 T, ∀ u ∈ V,
      η t * (ℓ t (x t) - ℓ t u) ≤ η t * (g t) (x t - u) ∧
      η t * (g t) (x t - u) ≤
        BeckTeboulleMD.EMDA.bregman ψ u (x t) -
          BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1)) -
          BeckTeboulleMD.EMDA.bregman ψ (x (t + 1)) (x t) +
          (η t) * (g t) (x t - x (t + 1)) ∧
      BeckTeboulleMD.EMDA.bregman ψ u (x t) -
          BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1)) -
          BeckTeboulleMD.EMDA.bregman ψ (x (t + 1)) (x t) +
          (η t) * (g t) (x t - x (t + 1)) ≤
        BeckTeboulleMD.EMDA.bregman ψ u (x t) -
          BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1)) +
          ((η t) ^ 2 / (2 * lam)) * ‖g t‖ ^ 2  := by
  intro t ht u hu
  rcases hrun.2 t ht with ⟨hη, hx, hy, horacle, hg, hm⟩
  have hdx : DifferentiableAt ℝ ψ (x t) :=
    (hψdiff _ hx.2).differentiableAt (isOpen_interior.mem_nhds hx.2)
  have hdy : DifferentiableAt ℝ ψ (x (t + 1)) :=
    (hψdiff _ hy.2).differentiableAt (isOpen_interior.mem_nhds hy.2)
  have hp : IsOMDStep V ψ (η t) (g t) (x t) (x (t+1)) :=
    ⟨hη, hx.1, hdx, hy.1, hm⟩
  refine ⟨?_, ?_, ?_⟩
  · have hs := hg u hu
    apply mul_le_mul_of_nonneg_left _ hη.le
    simp only [map_sub] at hs ⊢
    linarith
  · have hn := normal_condition V hVconv ψ (η t) (g t) (x t) (x (t + 1)) u hp hu hdy
    have hi := ModernOnlineLearning.OMD.lemma_6_7 X ψ hψstrict hψdiff
      (x (t + 1)) (x t) u hy.2 hx.2 (hVsub hu)
    simp only [ContinuousLinearMap.sub_apply, map_sub] at hn hi ⊢
    nlinarith
  · have hs : IsSubgradientOn (V ∩ interior X) ψ (x t) (fderiv ℝ ψ (x t)) := by
      intro z hz
      exact convex_support X ψ hψstrict.convexOn (x t) z (hVsub hx.1) (hVsub hz.1) hdx
    have hq := strong_support (V ∩ interior X) ψ lam hψstrong (x t) (x (t + 1)) hx hy _ hs
    have hb : lam / 2 * ‖x t - x (t + 1)‖ ^ 2 ≤ bregman ψ (x (t + 1)) (x t) := by
      dsimp only [bregman]
      linarith
    have hyb := young_bound ((η t) • g t) (x t - x (t + 1)) lam hlam
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_of_pos hη, mul_pow] at hyb
    have heq : ((η t) ^ 2 * ‖g t‖ ^ 2) / (2 * lam) = (η t) ^ 2 / (2 * lam) * ‖g t‖ ^ 2 := by ring
    rw [heq] at hyb
    linarith

