-- Prove2me | solution 1 for Goldstein1964.thm_ii_minimizes_of_convexOn_corrected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:29:33.735828+00:00
-- url     : https://prove2.me/submissions/fadc0291-9c7f-48b9-95d4-438ddf2120ec

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting
import Theorems.Thm_GoldsteinProj_Conv_goldstein_theorem
import Theorems.Thm_GoldsteinProj_Conv_isStationary_iff

open Filter Topology RealInnerProductSpace GoldsteinProj.Conv

namespace GS87

theorem fderiv_ineq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} {f : E → ℝ} (hf : ConvexOn ℝ C f) {x y : E}
    (hx : x ∈ C) (hy : y ∈ C) (hd : DifferentiableAt ℝ f x) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by
  let L := AffineMap.lineMap (k := ℝ) x y
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (f ∘ L) := by
    have h1 := hf.comp_affineMap L
    refine h1.subset ?_ (convex_Icc 0 1)
    intro s hs
    show L s ∈ C
    exact hf.1.lineMap_mem hx hy hs
  have hD : HasDerivAt (f ∘ L) (fderiv ℝ f x (y - x)) 0 := by
    have hL : HasDerivAt L (y - x) 0 := AffineMap.hasDerivAt_lineMap
    have hF : HasFDerivAt f (fderiv ℝ f x) (L 0) := by
      have : L 0 = x := by simp [L]
      rw [this]; exact hd.hasFDerivAt
    have := hF.comp_hasDerivAt (0 : ℝ) hL
    simpa using this
  have := hconv.le_slope_of_hasDerivAt (x := 0) (y := 1) (by simp) (by simp) one_pos hD
  rw [slope_def_field] at this
  simp [L] at this
  rw [map_sub]; linarith

end GS87

theorem solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCc : IsClosed C) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (hbdd : BddBelow (Set.range f)) (hfC : ContinuousOn f C)
    (hfconv : ConvexOn ℝ C f)
    (x0 : H) (hx0 : x0 ∈ C)
    (Shat : Set H) (hShat_open : IsOpen Shat) (hShat : convexHull ℝ (levelSet f C x0) ⊆ Shat)
    (ρ0 : ℝ) (hρ0 : 0 < ρ0) (hD : SecondDerivBound f Shat ρ0)
    (σ : ℝ) (hσ : 0 < σ) (hσρ0 : σ ≤ ρ0) (ρ : ℕ → ℝ) (x : ℕ → H)
    (hrun : IsGoldsteinRun f P x0 σ ρ0 ρ x)
    (hS : IsCompact (levelSet f C x0)) (z : H) (hz : MapClusterPt z atTop x)
    (hgrad : ∃ U ∈ 𝓝 z, ContinuousOn (gradient f) U)
    (huniq : ∀ z', MapClusterPt z' atTop x → z' = z) :
    Tendsto x atTop (𝓝 z) ∧ z ∈ C ∧ ∀ y ∈ C, f z ≤ f y := by
  obtain ⟨L, ⟨hmem, -, -, -⟩, hii, -⟩ := goldstein_theorem C hCc hCv P hP f hbdd hfC x0 hx0 Shat
    hShat_open hShat ρ0 hρ0 hD σ hσ hσρ0 ρ x hrun
  obtain ⟨hstat, htend⟩ := hii hS
  have hst := hstat z hz hgrad
  have hzC : z ∈ C := hst.1
  refine ⟨htend z hz huniq, hzC, ?_⟩
  -- z lies in the (closed) level set, hence in `Shat`, so `f` is differentiable at `z`
  have hzS : z ∈ levelSet f C x0 := by
    by_contra hzn
    have hev : ∀ᶠ w in 𝓝 z, w ∈ (levelSet f C x0)ᶜ :=
      hS.isClosed.isOpen_compl.mem_nhds hzn
    obtain ⟨k, hk⟩ := (hz.frequently hev).exists
    exact hk (hmem k)
  have hdiff : DifferentiableAt ℝ f z := (hD z (hShat (subset_convexHull ℝ _ hzS))).1
  have hmin := (isStationary_iff C hCv P hP f hfconv z hzC hdiff).1 hst
  intro y hy
  have h1 := GS87.fderiv_ineq hfconv hzC hy hdiff
  have h2 := hmin y hy
  rw [map_sub] at h1
  linarith
