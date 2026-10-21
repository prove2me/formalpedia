-- Prove2me | solution 1 for ModernOnlineLearning.OMD.lemma_6_10_exists
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:18:35.338448+00:00
-- url     : https://prove2.me/submissions/1ee6c54e-371e-44c4-b4af-d00d3d6772e1

import Definitions.Def_ModernOnlineLearning_OMD_Defs
import Theorems.Thm_ModernOnlineLearning_OMD_theorem_6_9

set_option autoImplicit false
open Filter Topology
open ModernOnlineLearning.OMD
open BeckTeboulleMD.EMDA (bregman)

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

private lemma closed_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X V : Set E) (ψ : E → ℝ) (A : E →L[ℝ] ℝ) (c : ℝ)
    (hc : IsClosedOnDomain X ψ) (hV : IsClosed V) (hVX : V ⊆ X) :
    IsClosedOnDomain V (fun z => ψ z + A z + c) := by
  have hmap : Continuous (fun p : E × ℝ => (p.1, p.2 - A p.1 - c)) := by fun_prop
  have hi := (hV.preimage continuous_fst).inter (hc.preimage hmap)
  have hset : {p : E × ℝ | p.1 ∈ V ∧ ψ p.1 + A p.1 + c ≤ p.2} =
      Prod.fst ⁻¹' V ∩ (fun p : E × ℝ => (p.1, p.2 - A p.1 - c)) ⁻¹'
        {p | p.1 ∈ X ∧ ψ p.1 ≤ p.2} := by
    ext p
    constructor
    · rintro ⟨hp, hle⟩
      exact ⟨hp, hVX hp, by dsimp only; linarith⟩
    · rintro ⟨hp, _, hle⟩
      exact ⟨hp, by dsimp only at hle ⊢; linarith⟩
  change IsClosed {p : E × ℝ | p.1 ∈ V ∧ ψ p.1 + A p.1 + c ≤ p.2}
  rw [hset]
  exact hi

private lemma strong_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (ψ : E → ℝ) (A : E →L[ℝ] ℝ) (c lam : ℝ)
    (hs : StrongConvexOn V lam ψ) : StrongConvexOn V lam (fun z => ψ z + A z + c) := by
  refine ⟨hs.1, fun x hx y hy a b ha hb hab => ?_⟩
  have h := hs.2 hx hy ha hb hab
  simp only [map_add, map_smul, smul_eq_mul] at h ⊢
  have hconst : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  nlinarith

private lemma step_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (X V : Set E) (ψ : E → ℝ) (lam : ℝ)
    (hsetting : IsOMDSetting X V ψ lam) (x : E) (hx : x ∈ V ∩ interior X)
    (η : ℝ) (hη : 0 < η) (g : E →L[ℝ] ℝ)
    (y : E) (hy : IsOMDStep V ψ η g x y) : y ∈ interior X := by
  rcases hsetting with ⟨_, hX, hstrict, hdiff, _, _, _, hV, hVX, hcond, _⟩
  have hyV := hy.2.2.2.1
  rcases hcond with hcond | hinter
  · by_contra hnot
    have hyfront : y ∈ frontier X := ⟨subset_closure (hVX hyV), hnot⟩
    have htend := hcond y hyfront x hx.2
    have hmin := (step_scaled V ψ η hη g x y hx.1 hy.2.2.1).mp hy
    have hbound : ∀ t : ℝ, 0 < t → t < 1 →
        fderiv ℝ ψ x (x - y) - η * g (x - y) ≤
          fderiv ℝ ψ ((1 - t) • y + t • x) (x - y) := by
      intro t ht ht1
      let z := (1 - t) • y + t • x
      have ha : 0 ≤ 1 - t := by linarith
      have hab : 1 - t + t = 1 := by ring
      have hzV : z ∈ V := hV hyV hx.1 ha ht.le hab
      have hzX : z ∈ interior X := hX.combo_self_interior_mem_interior (hVX hyV) hx.2 ha ht hab
      have hdz : DifferentiableAt ℝ ψ z := (hdiff z hzX).differentiableAt (isOpen_interior.mem_nhds hzX)
      have hs := convex_support X ψ hstrict.convexOn z y (hVX hzV) (hVX hyV) hdz
      have hm := hmin.2 z hzV
      have hzy : z - y = t • (x - y) := by dsimp [z]; module
      have hyz : y - z = -(t • (x - y)) := by rw [← hzy]; abel
      have hg : g z - g y = t * g (x - y) := by rw [← map_sub, hzy, map_smul]; rfl
      have hd : fderiv ℝ ψ x (z - x) - fderiv ℝ ψ x (y - x) = t * fderiv ℝ ψ x (x - y) := by
        rw [← map_sub]
        have heq : (z - x) - (y - x) = z - y := by abel
        rw [heq, hzy, map_smul]; rfl
      rw [hyz, map_neg, map_smul] at hs
      simp only [bregman, smul_eq_mul] at hm hs
      change fderiv ℝ ψ x (x - y) - η * g (x - y) ≤ fderiv ℝ ψ z (x - y)
      nlinarith
    have hsmall := htend.eventually (eventually_lt_atBot (fderiv ℝ ψ x (x - y) - η * g (x - y) - 1))
    have hall : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧ t < 1 ∧
        fderiv ℝ ψ ((1 - t) • y + t • x) (x - y) <
          fderiv ℝ ψ x (x - y) - η * g (x - y) - 1 := by
      filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)), hsmall] with t ht ht1 hsm
      exact ⟨ht, ht1, hsm⟩
    obtain ⟨t, ht, ht1, hsm⟩ := hall.exists
    have hb := hbound t ht ht1
    linarith
  · exact hinter hyV

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (X V : Set E) (ψ : E → ℝ) (lam : ℝ)
    (hsetting : IsOMDSetting X V ψ lam)
    (x : E) (hx : x ∈ V ∩ interior X)
    (η : ℝ) (hη : 0 < η) (g : E →L[ℝ] ℝ) :
    (∃! y : E, IsOMDStep V ψ η g x y) ∧
      ∀ y : E, IsOMDStep V ψ η g x y → y ∈ interior X := by
  refine ⟨?_, fun y hy => step_interior X V ψ lam hsetting x hx η hη g y hy⟩
  rcases hsetting with ⟨hlam, hX, hstrict, hdiff, hclosed, hVne, hVclosed, hV, hVX, hcond, hstrong⟩
  have hdx : DifferentiableAt ℝ ψ x := (hdiff x hx.2).differentiableAt (isOpen_interior.mem_nhds hx.2)
  let A : E →L[ℝ] ℝ := η • g - fderiv ℝ ψ x
  let c : ℝ := fderiv ℝ ψ x x - ψ x
  let H : E → ℝ := fun z => ψ z + A z + c
  have hc : IsClosedOnDomain V H := closed_affine X V ψ A c hclosed hVclosed hVX
  have hst : StrongConvexOn V lam H := strong_affine V ψ A c lam hstrong
  have hsub : IsSubgradientOn V H x (fderiv ℝ ψ x + A) := by
    intro z hz
    have hs := convex_support X ψ hstrict.convexOn x z (hVX hx.1) (hVX hz) hdx
    dsimp [H]
    simp only [ContinuousLinearMap.add_apply, map_sub] at hs ⊢
    linarith
  have hex := ModernOnlineLearning.OMD.theorem_6_9 V H lam hlam hc hst ⟨x, hx.1, _, hsub⟩
  have heq : ∀ z, H z = η * g z + bregman ψ z x := by
    intro z
    simp only [H, A, c, bregman, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, map_sub, smul_eq_mul]
    ring
  have hiff : ∀ y, IsOMDStep V ψ η g x y ↔ y ∈ V ∧ ∀ z ∈ V, H y ≤ H z := by
    intro y
    rw [step_scaled V ψ η hη g x y hx.1 hdx]
    simp only [heq]
  obtain ⟨y, hy, hu⟩ := hex
  exact ⟨y, (hiff y).mpr hy, fun z hz => hu z ((hiff z).mp hz)⟩

