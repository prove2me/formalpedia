-- Prove2me | solution 1 for MaxValSens.Wolfe.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:37:56.54498+00:00
-- url     : https://prove2.me/submissions/b303f4a1-033c-4db4-b06f-7bc4461183ce

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MaxValSens_Wolfe_Setting
open Filter Topology
open scoped InnerProductSpace

open MaxValSens.Wolfe in
theorem solution {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ) (x : E n)
    (hfc : ConcaveOn ℝ Set.univ (f x)) (hgc : ∀ i, ConvexOn ℝ Set.univ (g i x))
    (hfd : Differentiable ℝ (f x)) (hgd : ∀ i, Differentiable ℝ (g i x)) :
    V f g x ≤ VD f g x := by
  unfold V VD
  refine iSup₂_le fun y hy => le_iInf₂ fun p hp => ?_
  rw [EReal.coe_le_coe_iff]
  have hy' : ∀ i, g i x y ≤ 0 := hy
  obtain ⟨hgrad, hlam⟩ := hp
  obtain ⟨L, hL⟩ : ∃ L : E m → ℝ, L = fun z => Lag 1 f g x z p.2 := ⟨_, rfl⟩
  have hsum : ∀ s : Finset (Fin q),
      ConvexOn ℝ Set.univ (fun z => ∑ i ∈ s, p.2 i * g i x z) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simpa using (convexOn_const (0 : ℝ) convex_univ :
        ConvexOn ℝ Set.univ (fun _ : E m => (0 : ℝ)))
    | insert i s hi ih =>
      have h1 : ConvexOn ℝ Set.univ (fun z => p.2 i * g i x z) := by
        have := (hgc i).smul (hlam i)
        simpa only [smul_eq_mul] using this
      rw [show (fun z => ∑ j ∈ insert i s, p.2 j * g j x z)
          = (fun z => p.2 i * g i x z) + (fun z => ∑ j ∈ s, p.2 j * g j x z) from by
        funext z; simp [Finset.sum_insert hi]]
      exact h1.add ih
  have hLc : ConcaveOn ℝ Set.univ L := by
    have h := hfc.sub (hsum Finset.univ)
    have e : L = (f x - fun z => ∑ i ∈ Finset.univ, p.2 i * g i x z) := by
      funext z; simp [hL, Lag]
    rw [e]; exact h
  have hLd : DifferentiableAt ℝ L p.1 := by
    rw [hL]; unfold Lag
    have h2 : DifferentiableAt ℝ (fun z => ∑ i, p.2 i * g i x z) p.1 := by
      first
        | fun_prop
        | exact DifferentiableAt.fun_sum (fun i _ => ((hgd i) p.1).const_mul (p.2 i))
    exact ((hfd p.1).const_mul 1).sub h2
  have hfd0 : fderiv ℝ L p.1 = 0 := by
    have h : gradient L p.1 = 0 := by rw [hL]; exact hgrad
    unfold gradient at h
    simpa using congrArg (InnerProductSpace.toDual ℝ (E m)) h
  have hφ : HasDerivAt (L ∘ (AffineMap.lineMap p.1 y : ℝ →ᵃ[ℝ] E m))
      (fderiv ℝ L p.1 (y - p.1)) 0 :=
    hLd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) AffineMap.hasDerivAt_lineMap
      (AffineMap.lineMap_apply_zero _ _).symm
  have hφc : ConcaveOn ℝ Set.univ (L ∘ (AffineMap.lineMap p.1 y : ℝ →ᵃ[ℝ] E m)) := by
    simpa using hLc.comp_affineMap (AffineMap.lineMap p.1 y : ℝ →ᵃ[ℝ] E m)
  have hs := hφc.slope_le_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hφ
  rw [hfd0, slope_def_field] at hs
  simp only [Function.comp, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, sub_zero,
    div_one, ContinuousLinearMap.zero_apply] at hs
  have hLy : f x y ≤ L y := by
    rw [hL]
    show f x y ≤ 1 * f x y - ∑ i, p.2 i * g i x y
    have : ∑ i, p.2 i * g i x y ≤ 0 :=
      Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (hy' i)
    linarith
  have hLp : L p.1 = Lag 1 f g x p.1 p.2 := by rw [hL]
  linarith
