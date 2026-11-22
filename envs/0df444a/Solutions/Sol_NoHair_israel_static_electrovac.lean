-- Prove2me | solution 1 for NoHair.israel_static_electrovac
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:52:47.968064+00:00
-- url     : https://prove2.me/submissions/7706912a-de79-45aa-bee7-85f7482cb8f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_static_electrovac_spherical_exterior
import Theorems.Thm_NoHair_spherical_electrovac_radial_equations
import Theorems.Thm_NoHair_reissnerNordstrom_lapse_of_radial_equation

open scoped ContDiff Manifold BigOperators
open Set NoHair

private theorem flux_constant {R : ℝ} {f : ℝ → ℝ}
    (h : ∀ r, R < r → HasDerivAt f 0 r) : ∃ q, ∀ r, R < r → f r = q :=
  isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun r hr => (h r hr).differentiableAt.differentiableWithinAt)
    (fun {r} hr => (h r hr).deriv)

private theorem coulomb_field_scale (e : ℝ) (y : E4) :
    kerrNewmanField 0 e y = e • kerrNewmanField 0 1 y := by
  have hpot (i : Fin 4) :
      (fun z => kerrNewmanPotential 0 e z i) = e • (fun z => kerrNewmanPotential 0 1 z i) := by
    funext z
    simp only [kerrNewmanPotential, Pi.smul_apply, smul_eq_mul, one_mul]
    ring
  ext i j
  simp only [kerrNewmanField, coordPartial, hpot, fderiv_const_smul_field, Pi.smul_apply,
    smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem hodgeDual_scale (G B : Matrix (Fin 4) (Fin 4) ℝ) (e : ℝ) :
    hodgeDual G (e • B) = e • hodgeDual G B := by
  ext i j
  simp only [hodgeDual, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  iterate 4 (apply Finset.sum_congr rfl; intro k hk)
  ring

theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hstatic : IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ m e : ℝ, IsKerrNewmanBlackHoleParams m 0 e ∧
      IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m 0 e := by
  obtain ⟨S⟩ := static_electrovac_spherical_exterior g F T φ E h hstatic
  have radial := spherical_electrovac_radial_equations g F S h.lorentzian h.smooth_metric
    h.smooth_field h.twoForm h.electrovac
  obtain ⟨q, hq⟩ := flux_constant (fun r hr => (radial r hr).1)
  obtain ⟨p, hp⟩ := flux_constant (fun r hr => (radial r hr).2.1)
  let z : ℂ := ⟨q, p⟩
  let e := ‖z‖
  have he : e ^ 2 = q ^ 2 + p ^ 2 := by
    change ‖(⟨q, p⟩ : ℂ)‖ ^ 2 = _
    rw [Complex.sq_norm, Complex.normSq_mk]
    ring
  have hcos : Real.cos z.arg * e = q := by rw [mul_comm]; exact Complex.norm_mul_cos_arg z
  have hsin : Real.sin z.arg * e = p := by rw [mul_comm]; exact Complex.norm_mul_sin_arg z
  have hrad (r : ℝ) (hr : S.horizonRadius < r) :
      HasDerivAt (fun s => s * (1 - S.lapseSq s)) (e ^ 2 / r ^ 2) r := by
    simpa only [he, hq r hr, hp r hr] using (radial r hr).2.2
  obtain ⟨m, hm, hbound, houter, hprofile⟩ :=
    reissnerNordstrom_lapse_of_radial_equation S.horizonRadius e S.lapseSq S.radius_pos
      S.lapse_continuous S.lapse_horizon S.lapse_pos hrad
  have hradius : kerrNewmanOuterRadius m 0 e = S.horizonRadius := by
    simpa [kerrNewmanOuterRadius] using houter.symm
  have hdoc : kerrNewmanDOC m 0 e = {y | S.horizonRadius < ksRadius 0 y} := by
    unfold kerrNewmanDOC
    rw [hradius]
  refine ⟨m, e, ⟨hm, by simpa using hbound⟩, z.arg, S.chart, hdoc ▸ S.diffeo, ?_⟩
  intro y hy
  rw [hdoc] at hy
  have hr : S.horizonRadius < ksRadius 0 y := hy
  have hr0 := (lt_trans S.radius_pos hr).ne'
  have hk : ksProfile m 0 e y = 1 - S.lapseSq (ksRadius 0 y) := by
    simp only [ksProfile, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero]
    apply (div_eq_iff (pow_ne_zero 4 hr0)).2
    rw [← hprofile _ hr]
    ring
  have hg : pullbackCoeffs g S.chart y = kerrNewmanMetric m 0 e y := by
    rw [S.metric_coeffs y hr]
    ext i j
    simp only [kerrNewmanMetric, hk]
  refine ⟨hg, ?_⟩
  rw [S.field_coeffs y hr, hq _ hr, hp _ hr, hg, coulomb_field_scale e y,
    hodgeDual_scale, smul_smul, smul_smul, hcos, hsin]
