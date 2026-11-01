-- Prove2me | solution 1 for MaxValSens.Wolfe.theorem_3_3_eq_3_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:19:37.979491+00:00
-- url     : https://prove2.me/submissions/3ab13b73-9922-4efa-a6d9-e01a63feba38

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MaxValSens_Wolfe_Setting
import Definitions.Def_Polyhedron
import Theorems.Thm_MaxValSens_Wolfe_theorem_3_3_kkt
import Theorems.Thm_MaxValSens_Wolfe_lemma_3_1
import Theorems.Thm_LinearOptimization_polyhedron_linear_image
import Theorems.Thm_LinearOptimization_polyhedron_closed
open Filter Topology
open scoped InnerProductSpace

namespace MaxValSens.Wolfe

/-- The image of a polyhedron `{u | ∀ i, cᵢ ≤ ℓᵢ u}` under a linear map is closed. -/
private lemma isClosed_image_poly' {k l : ℕ} {ι : Type} [Fintype ι] (T : E k →L[ℝ] E l)
    (ℓ : ι → E k →L[ℝ] ℝ) (c : ι → ℝ) :
    IsClosed (T '' {u | ∀ i, c i ≤ ℓ i u}) := by
  classical
  let eι := Fintype.equivFin ι
  let ek := EuclideanSpace.equiv (Fin k) ℝ
  let el := EuclideanSpace.equiv (Fin l) ℝ
  let Lmap : (Fin k → ℝ) →ₗ[ℝ] (Fin (Fintype.card ι) → ℝ) :=
    LinearMap.pi (fun j => (ℓ (eι.symm j)).toLinearMap.comp ek.symm.toLinearMap)
  let Mmap : (Fin k → ℝ) →ₗ[ℝ] (Fin l → ℝ) :=
    (el.toLinearMap.comp T.toLinearMap).comp ek.symm.toLinearMap
  let A := LinearMap.toMatrix' Lmap
  let M := LinearMap.toMatrix' Mmap
  let b : Fin (Fintype.card ι) → ℝ := fun j => c (eι.symm j)
  obtain ⟨m', A', b', h⟩ := LinearOptimization.polyhedron_linear_image A b M
  have hc := LinearOptimization.polyhedron_closed A' b'
  rw [← h] at hc
  have hA : ∀ v, A.mulVec v = Lmap v := fun v => LinearMap.toMatrix'_mulVec Lmap v
  have hM : ∀ v, M.mulVec v = Mmap v := fun v => LinearMap.toMatrix'_mulVec Mmap v
  have heq : T '' {u | ∀ i, c i ≤ ℓ i u} =
      el.symm.toHomeomorph '' (M.mulVec '' LinearOptimization.polyhedron A b) := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨M.mulVec (ek u), ⟨ek u, ?_, rfl⟩, ?_⟩
      · show b ≤ A.mulVec (ek u)
        rw [hA]
        intro j
        show c (eι.symm j) ≤ ℓ (eι.symm j) (ek.symm (ek u))
        rw [ContinuousLinearEquiv.symm_apply_apply]
        exact hu _
      · rw [hM]
        show el.symm (el (T (ek.symm (ek u)))) = T u
        simp
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨ek.symm v, fun i => ?_, ?_⟩
      · have hv' : b ≤ A.mulVec v := hv
        rw [hA] at hv'
        have := hv' (eι i)
        simpa [b, Lmap] using this
      · rw [hM]
        show T (ek.symm v) = el.symm (el (T (ek.symm v)))
        simp
  rw [heq]
  exact (Homeomorph.isClosed_image _).mpr hc

private lemma lag_contDiff'' {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) :
    ContDiff ℝ 2 (fun z : E n × E m × (Fin q → ℝ) => Lag 1 f g z.1 z.2.1 z.2.2) := by
  unfold Lag
  have h1 : ContDiff ℝ 2 (fun z : E n × E m × (Fin q → ℝ) => (z.1, z.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  apply ContDiff.sub
  · exact contDiff_const.mul (hf.comp h1)
  · apply ContDiff.sum
    intro i _
    exact ((contDiff_apply ℝ ℝ i).comp (contDiff_snd.comp contDiff_snd)).mul ((hg i).comp h1)

/-- `u ↦ ∇²_xy L(x, y, λ) u` is a continuous linear map (the adjoint of `D_x ∇_y L`). -/
private lemma hessXY_clm' {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2))
    (x : E n) (y : E m) (l : Fin q → ℝ) :
    ∃ T : E m →L[ℝ] E n, ∀ u, hessXY f g x y l u = T u := by
  set Φ := fun z : E n × E m × (Fin q → ℝ) => Lag 1 f g z.1 z.2.1 z.2.2 with hΦdef
  have hΦ : ContDiff ℝ 2 Φ := lag_contDiff'' f g hf hg
  let J : E m →L[ℝ] E n × E m × (Fin q → ℝ) :=
    (0 : E m →L[ℝ] E n).prod ((ContinuousLinearMap.id ℝ (E m)).prod 0)
  have hG : ∀ x', gradY 1 f g x' y l =
      (InnerProductSpace.toDual ℝ (E m)).symm ((fderiv ℝ Φ (x', y, l)).comp J) := by
    intro x'
    unfold gradY gradient
    congr 1
    have hd : DifferentiableAt ℝ Φ (x', y, l) :=
      (hΦ.differentiable (by norm_num)).differentiableAt
    have hi : HasFDerivAt (fun y' : E m => ((x', y', l) : E n × E m × (Fin q → ℝ))) J y :=
      (hasFDerivAt_const x' y).prodMk ((hasFDerivAt_id y).prodMk (hasFDerivAt_const l y))
    exact (hd.hasFDerivAt.comp y hi).fderiv
  have hGd : DifferentiableAt ℝ (fun x' => gradY 1 f g x' y l) x := by
    rw [show (fun x' => gradY 1 f g x' y l) = fun x' =>
      (InnerProductSpace.toDual ℝ (E m)).symm ((fderiv ℝ Φ (x', y, l)).comp J) from funext hG]
    have h1 : Differentiable ℝ (fderiv ℝ Φ) :=
      (hΦ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    have h2 : DifferentiableAt ℝ (fun x' : E n => ((x', y, l) : E n × E m × (Fin q → ℝ))) x :=
      differentiableAt_id.prodMk (differentiableAt_const _)
    have h3 : DifferentiableAt ℝ (fun x' : E n => (fderiv ℝ Φ (x', y, l)).comp J) x :=
      ((h1 _).comp x h2).clm_comp (differentiableAt_const J)
    exact (InnerProductSpace.toDual ℝ (E m)).symm.toContinuousLinearEquiv.differentiableAt.comp x h3
  set D := fderiv ℝ (fun x' => gradY 1 f g x' y l) x with hD
  refine ⟨ContinuousLinearMap.adjoint D, fun u => ?_⟩
  unfold hessXY gradient
  have hu : HasFDerivAt (fun x' => ⟪gradY 1 f g x' y l, u⟫_ℝ) ((innerSL ℝ u).comp D) x := by
    have := (innerSL ℝ u).hasFDerivAt.comp x hGd.hasFDerivAt
    have hfun : (fun x' => ⟪gradY 1 f g x' y l, u⟫_ℝ) =
        (innerSL ℝ u) ∘ (fun x' => gradY 1 f g x' y l) := by
      funext x'
      simp [real_inner_comm]
    rw [hfun]
    exact this
  rw [hu.fderiv]
  apply ext_inner_right ℝ
  intro v
  rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.adjoint_inner_left]
  simp

end MaxValSens.Wolfe

open MaxValSens.Wolfe

theorem solution {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (xbar : E n) (ybar : E m) (lambar : Fin q → ℝ)
    (hS : Standing f g xbar) (hy : ybar ∈ S f g xbar) (hlam : lambar ∈ SigmaM 1 f g xbar ybar)
    (hCQ : LocalErrorBound311 f g (xbar, ybar, lambar)) :
    {ξ | NonconvexSplitting.Shared.IsRegularSubgrad (V f g) xbar ξ} ⊆
      {ξ | ∃ u ∈ Xi 1 f g xbar ybar lambar,
        ξ = gradX f g xbar ybar lambar + hessXY f g xbar ybar lambar u} := by
  intro ξ hξ
  have hdiff : ∀ x : E n, Differentiable ℝ (f x) ∧ ∀ i, Differentiable ℝ (g i x) := by
    intro x
    refine ⟨fun y' => ((hS.1.differentiable (by norm_num)) (x, y')).comp y'
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y').differentiableAt, fun i y' =>
      (((hS.2.1 i).differentiable (by norm_num)) (x, y')).comp y'
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y').differentiableAt⟩
  -- Step 1: `(x̄, ȳ, λ̄)` is a local minimizer of (3.16) for every `ε > 0`.
  have hmin : ∀ ε : ℝ, 0 < ε → IsLocalMinOn (fun z : E n × E m × (Fin q → ℝ) =>
        Lag 1 f g z.1 z.2.1 z.2.2 - ⟪ξ, z.1 - xbar⟫_ℝ + ε * ‖z.1 - xbar‖)
      (Sys311 f g) (xbar, ybar, lambar) := by
    intro ε hε
    have h3 : ∀ᶠ z in 𝓝 ((xbar, ybar, lambar) : E n × E m × (Fin q → ℝ)),
        (V f g xbar + ((⟪ξ, z.1 - xbar⟫_ℝ - ε * ‖z.1 - xbar‖ : ℝ) : EReal) ≤ V f g z.1) ∧
        (ConcaveOn ℝ Set.univ (f z.1) ∧ ∀ i, ConvexOn ℝ Set.univ (g i z.1)) :=
      (continuous_fst.tendsto ((xbar, ybar, lambar) : E n × E m × (Fin q → ℝ))).eventually
        ((hξ.2 ε hε).and hS.2.2)
    filter_upwards [nhdsWithin_le_nhds h3, self_mem_nhdsWithin] with z hz hzS
    obtain ⟨hV, hfc, hgc⟩ := hz
    have hw := lemma_3_1 f g z.1 hfc hgc (hdiff z.1).1 (hdiff z.1).2
    have hD : VD f g z.1 ≤ ((Lag 1 f g z.1 z.2.1 z.2.2 : ℝ) : EReal) := by
      unfold VD
      exact iInf₂_le (f := fun p (_ : p ∈ DualFeas f g z.1) =>
        ((Lag 1 f g z.1 p.1 p.2 : ℝ) : EReal)) (z.2.1, z.2.2) hzS
    have hVx : V f g xbar = ((f xbar ybar : ℝ) : EReal) := hy.2.symm
    rw [hVx, ← EReal.coe_add] at hV
    have hreal := EReal.coe_le_coe_iff.mp (hV.trans (hw.trans hD))
    have hL : Lag 1 f g xbar ybar lambar = f xbar ybar := by
      unfold Lag
      rw [Finset.sum_eq_zero (fun i _ => (hlam.2 i).2.2), one_mul, sub_zero]
    show Lag 1 f g xbar ybar lambar - ⟪ξ, xbar - xbar⟫_ℝ + ε * ‖xbar - xbar‖ ≤ _
    simp only [sub_self, inner_zero_right, norm_zero, mul_zero, sub_zero, add_zero]
    rw [hL]
    linarith
  -- Step 2: the KKT conditions of (3.16) give ε-approximate representations.
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ u ∈ Xi 1 f g xbar ybar lambar,
      ‖ξ - (gradX f g xbar ybar lambar + hessXY f g xbar ybar lambar u)‖ ≤ ε :=
    fun ε hε => theorem_3_3_kkt f g xbar ybar lambar ξ ε hS.1 hS.2.1 hε (hmin ε hε) hCQ
  -- Step 3: the right-hand side of (3.12) is closed (a translate of a linear image of a
  -- polyhedron).
  obtain ⟨T, hT⟩ := hessXY_clm' f g hS.1 hS.2.1 xbar ybar lambar
  set H := fderiv ℝ (fun y' => gradY 1 f g xbar y' lambar) ybar with hH
  let ℓ : (Fin m ⊕ Fin m) ⊕ (Fin q ⊕ Fin q) → E m →L[ℝ] ℝ := fun k =>
    match k with
    | Sum.inl (Sum.inl j) => (EuclideanSpace.proj j).comp H
    | Sum.inl (Sum.inr j) => -((EuclideanSpace.proj j).comp H)
    | Sum.inr (Sum.inl i) => -(fderiv ℝ (g i xbar) ybar)
    | Sum.inr (Sum.inr i) => lambar i • fderiv ℝ (g i xbar) ybar
  let c : (Fin m ⊕ Fin m) ⊕ (Fin q ⊕ Fin q) → ℝ := fun k =>
    match k with
    | Sum.inl (Sum.inl _) => 0
    | Sum.inl (Sum.inr _) => 0
    | Sum.inr (Sum.inl i) => g i xbar ybar
    | Sum.inr (Sum.inr i) => -(lambar i * g i xbar ybar)
  have hXi : Xi 1 f g xbar ybar lambar = {u | ∀ k, c k ≤ ℓ k u} := by
    ext u
    constructor
    · rintro ⟨h1, h2⟩ k
      have h1' : H u = 0 := h1
      rcases k with (j | j) | (i | i)
      · show (0 : ℝ) ≤ (H u) j
        rw [h1']; simp
      · show (0 : ℝ) ≤ -((H u) j)
        rw [h1']; simp
      · show g i xbar ybar ≤ -(fderiv ℝ (g i xbar) ybar u)
        have := (h2 i).2.1
        unfold dgY at this
        linarith
      · show -(lambar i * g i xbar ybar) ≤ lambar i * (fderiv ℝ (g i xbar) ybar u)
        have := (h2 i).2.2
        unfold dgY at this
        linarith
    · intro h
      refine ⟨?_, fun i => ?_⟩
      · show H u = 0
        ext j
        have a1 : (0 : ℝ) ≤ (H u) j := h (Sum.inl (Sum.inl j))
        have a2 : (0 : ℝ) ≤ -((H u) j) := h (Sum.inl (Sum.inr j))
        simp only [PiLp.zero_apply]
        linarith
      · have a3 : g i xbar ybar ≤ -(fderiv ℝ (g i xbar) ybar u) := h (Sum.inr (Sum.inl i))
        have a4 : -(lambar i * g i xbar ybar) ≤ lambar i * (fderiv ℝ (g i xbar) ybar u) :=
          h (Sum.inr (Sum.inr i))
        have hl0 := (hlam.2 i).1
        unfold dgY
        refine ⟨hl0, by linarith, ?_⟩
        apply le_antisymm
        · linarith
        · exact mul_nonneg hl0 (by linarith)
  have hclosed : IsClosed {w | ∃ u ∈ Xi 1 f g xbar ybar lambar,
      w = gradX f g xbar ybar lambar + hessXY f g xbar ybar lambar u} := by
    have himg : {w | ∃ u ∈ Xi 1 f g xbar ybar lambar,
        w = gradX f g xbar ybar lambar + hessXY f g xbar ybar lambar u} =
        (Homeomorph.addLeft (gradX f g xbar ybar lambar)) '' (T '' {u | ∀ k, c k ≤ ℓ k u}) := by
      ext w
      constructor
      · rintro ⟨u, hu, rfl⟩
        rw [hXi] at hu
        exact ⟨T u, ⟨u, hu, rfl⟩, by simp [hT]⟩
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        rw [← hXi] at hu
        exact ⟨u, hu, by simp [hT]⟩
    rw [himg]
    exact (Homeomorph.isClosed_image _).mpr (isClosed_image_poly' T ℓ c)
  -- Step 4: `ξ` lies in the closure, hence in the set.
  have hcl : ξ ∈ closure {w | ∃ u ∈ Xi 1 f g xbar ybar lambar,
      w = gradX f g xbar ybar lambar + hessXY f g xbar ybar lambar u} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨u, hu, hle⟩ := happrox (ε / 2) (by linarith)
    exact ⟨_, ⟨u, hu, rfl⟩, by rw [dist_eq_norm]; linarith⟩
  rw [hclosed.closure_eq] at hcl
  exact hcl
