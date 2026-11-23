-- Prove2me | solution 1 for NoHair.signed_static_lapse_harmonic_factor
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T07:20:07.843901+00:00
-- url     : https://prove2.me/submissions/af041a2a-3e77-45f7-8ab7-a7c4fdc26d5d

import Mathlib

open Set Filter Topology InnerProductSpace
open scoped Laplacian ContDiff

private abbrev X := EuclideanSpace ℝ (Fin 3)
private noncomputable abbrev b (i : Fin 3) : X := EuclideanSpace.single i 1

theorem solution (V : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hreg : ContDiffOn ℝ 2 V ({0}ᶜ)) (hlower : ∀ x, x ≠ 0 → -1 < V x)
    (hflux : ∀ x : EuclideanSpace ℝ (Fin 3), x ≠ 0 → V x ≠ 0 →
        ∑ i : Fin 3, fderiv ℝ
          (fun y => (2 / (1 + V y))^2 * fderiv ℝ V y (EuclideanSpace.single i (1:ℝ)))
          x (EuclideanSpace.single i (1:ℝ)) = 0) :
    HarmonicOnNhd (fun x => 2 / (1 + V x)) ({0}ᶜ) := by
  let U := fun x : X => 2 / (1 + V x)
  have cv (x : X) (hx : x ≠ 0) : ContDiffAt ℝ 2 V x :=
    hreg.contDiffAt (isOpen_compl_singleton.mem_nhds hx)
  have dn (x : X) (hx : x ≠ 0) : 1 + V x ≠ 0 := by
    have h := hlower x hx
    linarith
  have cu (x : X) (hx : x ≠ 0) : ContDiffAt ℝ 2 U x :=
    contDiffAt_const.div (contDiffAt_const.add (cv x hx)) (dn x hx)
  have flux_id (x : X) (hx : x ≠ 0) (i : Fin 3) :
      U x ^ 2 * fderiv ℝ V x (b i) = (-2) * fderiv ℝ U x (b i) := by
    have q : HasDerivAt (fun t : ℝ => 2 / (1 + t)) (-2 / (1 + V x)^2) (V x) := by
      simpa using (hasDerivAt_const (V x) (2:ℝ)).fun_div
        ((hasDerivAt_id (V x)).const_add 1) (dn x hx)
    have du : fderiv ℝ U x = (-2 / (1 + V x)^2) • fderiv ℝ V x :=
      (q.comp_hasFDerivAt x ((cv x hx).differentiableAt (by norm_num)).hasFDerivAt).fderiv
    rw [du, ContinuousLinearMap.smul_apply, smul_eq_mul]
    dsimp only [U]
    field_simp [dn x hx]
    <;> ring
  have term (x : X) (hx : x ≠ 0) (i : Fin 3) :
      fderiv ℝ (fun y => U y ^ 2 * fderiv ℝ V y (b i)) x (b i) =
      (-2) * iteratedFDeriv ℝ 2 U x ![b i,b i] := by
    have eq : (fun y => U y ^ 2 * fderiv ℝ V y (b i)) =ᶠ[𝓝 x]
        (fun y => (-2) * fderiv ℝ U y (b i)) := by
      filter_upwards [eventually_ne_nhds hx] with y hy using flux_id y hy i
    have c : DifferentiableAt ℝ (fderiv ℝ U) x :=
      ((cu x hx).fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero
    have cd : DifferentiableAt ℝ (fun y => fderiv ℝ U y (b i)) x :=
      c.clm_apply (differentiableAt_const (b i))
    rw [eq.fderiv_eq, fderiv_const_mul cd, ContinuousLinearMap.smul_apply, smul_eq_mul,
      iteratedFDeriv_two_apply]
    rw [fderiv_clm_apply (u := fun _ : X => b i) c (differentiableAt_const (b i))]
    simp
  have trace (x : X) : (Δ U) x = ∑ i : Fin 3, iteratedFDeriv ℝ 2 U x ![b i,b i] := by
    simpa only [EuclideanSpace.basisFun_apply,b] using congrFun
      (laplacian_eq_iteratedFDeriv_orthonormalBasis U (EuclideanSpace.basisFun (Fin 3) ℝ)) x
  have off (x : X) (hx : x ≠ 0) (hv : V x ≠ 0) : (Δ U) x = 0 := by
    have e := hflux x hx hv
    change ∑ i : Fin 3, fderiv ℝ (fun y => U y^2 * fderiv ℝ V y (b i)) x (b i) = 0 at e
    simp_rw [term x hx] at e
    rw [← Finset.mul_sum, ← trace] at e
    linarith
  have lap (x:X) (hx:x ≠ 0) : (Δ U) x = 0 := by
    have c (i : Fin 3) : ContinuousAt (fun y => iteratedFDeriv ℝ 2 U y ![b i,b i]) x :=
      (continuous_eval_const ![b i,b i]).continuousAt.comp
        ((cu x hx).continuousAt_iteratedFDeriv (k:=2) (by norm_num))
    have cl : ContinuousAt (Δ U) x := by
      rw [show Δ U = fun z => ∑ i : Fin 3, iteratedFDeriv ℝ 2 U z ![b i,b i] from funext trace]
      simp only [Fin.sum_univ_three]
      exact ((c 0).add (c 1)).add (c 2)
    by_contra bad
    have fixed : U =ᶠ[𝓝 x] (fun _ => (2:ℝ)) := by
      filter_upwards [cl.eventually_ne bad,eventually_ne_nhds hx] with y hy hn
      have vz : V y = 0 := by
        by_contra nz
        exact hy (off y hn nz)
      simp only [U,vz,add_zero,div_one]
    have bound := (laplacian_congr_nhds fixed).self_of_nhds
    exact bad (by simpa only [laplacian_const,Pi.zero_apply] using bound)
  intro x hx
  refine ⟨cu x hx,?_⟩
  filter_upwards [eventually_ne_nhds (show x ≠ 0 from hx)] with y hy using lap y hy
