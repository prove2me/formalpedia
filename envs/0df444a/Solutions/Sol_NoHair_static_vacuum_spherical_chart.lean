-- Prove2me | solution 1 for NoHair.static_vacuum_spherical_chart
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:34:47.316374+00:00
-- url     : https://prove2.me/submissions/3234e2e3-785e-4aea-a068-faf7bf406ba7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_static_vacuum_conformal_double
import Theorems.Thm_NoHair_punctured_conformal_factor
import Theorems.Thm_NoHair_schwarzschild_isotropic_exterior_change
import Theorems.Thm_NoHair_ingoing_areal_angular_ricci
import Definitions.Def_NoHair_sphericalArealExterior

open NoHair Set
open scoped ContDiff Manifold

private lemma compose_charts {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] {f : E4 → E4} {g : E4 → M} {S U : Set E4} {D : Set M}
    (hf : IsDiffeoOnto f S U) (hg : IsDiffeoOnto g U D) : IsDiffeoOnto (g ∘ f) S D := by
  obtain ⟨j, hfu, hjs, hjf, hfj, hdf, hdj⟩ := hf
  obtain ⟨k, hgd, hku, hkg, hgk, hdg, hdk⟩ := hg
  refine ⟨j ∘ k, hgd.comp hfu, hjs.comp hku, ?_, ?_, hdg.comp hdf hfu, hdj.comp hdk hku⟩
  · intro x hx
    change j (k (g (f x))) = x
    rw [hkg (hfu hx), hjf hx]
  · intro x hx
    change g (f (j (k x))) = x
    rw [hfj (hku hx), hgk hx]

private lemma spatial_cont : Continuous conformalSpatialPoint := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> change Continuous (fun x : E4 => x _) <;> fun_prop

private lemma positive_side (b : ℝ) (hb : 0 < b) :
    conformalExteriorDomain (fun x => 1 + b / ‖x‖) = {y | b < ‖conformalSpatialPoint y‖} := by
  ext y
  change (conformalSpatialPoint y ≠ 0 ∧ 1 + b / ‖conformalSpatialPoint y‖ < 2) ↔ _
  constructor
  · rintro ⟨hn, h⟩
    exact (div_lt_one (norm_pos_iff.mpr hn)).mp (by linarith)
  · intro h
    change b < ‖conformalSpatialPoint y‖ at h
    exact ⟨norm_pos_iff.mp (hb.trans h), by
      have hlo := (div_lt_one (hb.trans h)).mpr h
      linarith⟩

theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0) (hstatic : IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ S : SphericalArealExterior g F (domainOfOuterCommunications g T E.region),
      (∀ r, S.horizonRadius < r → DifferentiableAt ℝ S.lapseSq r) ∧
      ∀ r, S.horizonRadius < r →
        let G := fun y : E4 => !![-S.lapseSq (y 1), 1, 0, 0;
          1, 0, 0, 0; 0, 0, y 1 ^ 2 / (1 - y 2 ^ 2), 0;
          0, 0, 0, y 1 ^ 2 * (1 - y 2 ^ 2)]
        ricci G (WithLp.toLp 2 ![0, r, 0, 0]) 3 3 = 0 := by
  obtain ⟨b, U, hb, hharm, hfar, horigin, ho, ψ, hψ, hmetric⟩ :=
    static_vacuum_conformal_double g F T φ E h hvac hstatic
  let V := fun x : EuclideanSpace ℝ (Fin 3) => 1 + b / ‖x‖
  have hV := punctured_conformal_factor U b hharm hfar horigin
  have hdom : conformalExteriorDomain U = conformalExteriorDomain V := by
    ext z
    change (_ ≠ 0 ∧ U _ < 2) ↔ (_ ≠ 0 ∧ V _ < 2)
    constructor <;> rintro ⟨hz, hlt⟩ <;> exact ⟨hz, by simpa only [hV _ hz, V] using hlt⟩
  rw [hdom] at hψ hmetric
  obtain ⟨H, hH, hHM⟩ := schwarzschild_isotropic_exterior_change b hb
  have hchart := compose_charts hH hψ
  let m := 2 * b
  let R := 4 * b
  have hR : 0 < R := by dsimp only [R]; positivity
  have hm : 0 < m := by dsimp only [m]; positivity
  have outer : kerrNewmanOuterRadius m 0 0 = R := by
    simp only [kerrNewmanOuterRadius, zero_pow (by decide : 2 ≠ 0), sub_zero, Real.sqrt_sq hm.le]
    dsimp only [m, R]
    ring
  have harea : kerrNewmanDOC m 0 0 = {y | R < ksRadius 0 y} := by
    simp [kerrNewmanDOC, outer]
  have hop : IsOpen (kerrNewmanDOC m 0 0) := by
    rw [harea]
    exact isOpen_lt continuous_const (by unfold ksRadius; fun_prop)
  have hvop : IsOpen (conformalExteriorDomain V) := by
    rw [positive_side b hb]
    exact isOpen_lt continuous_const spatial_cont.norm
  obtain ⟨_, hmapH, _, _, _, hsH, _⟩ := hH
  obtain ⟨_, _, _, _, _, hsψ, _⟩ := hψ
  have pulled (y : E4) (hy : R < ksRadius 0 y) :
      pullbackCoeffs g (ψ ∘ H) y = kerrNewmanMetric m 0 0 y := by
    have hk : y ∈ kerrNewmanDOC m 0 0 := by rw [harea]; exact hy
    have hv : H y ∈ conformalExteriorDomain V := hmapH hk
    have dH := ((hsH y hk).contMDiffAt (hop.mem_nhds hk)).mdifferentiableAt (by simp)
    have dψ := ((hsψ _ hv).contMDiffAt (hvop.mem_nhds hv)).mdifferentiableAt (by simp)
    ext i j
    simp only [pullbackCoeffs, Function.comp_apply, mfderiv_comp (I' := 𝓘(ℝ, E4)) y dψ dH,
      ContinuousLinearMap.comp_apply]
    calc
      _ = conformalStaticForm (U (conformalSpatialPoint (H y)))
            (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) H y (coordBasis i))
            (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) H y (coordBasis j)) := hmetric (H y) hv _ _
      _ = _ := by rw [hV _ hv.1]; exact hHM y hk i j
  let A := fun r : ℝ => 1 - R * r⁻¹
  have dA (r : ℝ) (hr : 0 < r) : HasDerivAt A (R / r ^ 2) r := by
    apply ((hasDerivAt_const r (1 : ℝ)).fun_sub ((hasDerivAt_inv hr.ne').const_mul R)).congr_deriv
    field_simp [hr.ne'] <;> ring
  let S : SphericalArealExterior g F (domainOfOuterCommunications g T E.region) := {
    horizonRadius := R
    radius_pos := hR
    chart := ψ ∘ H
    isOpen_domain := ho
    diffeo := harea ▸ hchart
    lapseSq := A
    electricFlux := fun _ => 0
    magneticFlux := fun _ => 0
    lapse_continuous := fun r hr => (dA r (hR.trans_le hr)).continuousAt.continuousWithinAt
    lapse_horizon := by dsimp only [A]; field_simp [hR.ne'] <;> ring
    lapse_pos := fun r hr => by
      dsimp only [A]
      rw [← div_eq_mul_inv]
      linarith only [(div_lt_one (hR.trans hr)).mpr hr]
    metric_coeffs := fun y hy => by
      rw [pulled y hy]
      have hpr : ksProfile m 0 0 y = R / ksRadius 0 y := by
        simp only [ksProfile, zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero, add_zero, m, R]
        field_simp [(hR.trans hy).ne'] <;> ring
      ext i j
      simp only [kerrNewmanMetric, hpr, A]
      ring
    field_coeffs := fun y _ => by ext i j; simp [pullbackCoeffs, hvac] }
  refine ⟨S, fun r hr => (dA r (hR.trans hr)).differentiableAt, ?_⟩
  intro r hr
  change R < r at hr
  apply (ingoing_areal_angular_ricci A R r (hR.trans hr) hr
    (fun x hx => (dA x (hR.trans hx)).differentiableAt)).trans
  rw [(dA r (hR.trans hr)).deriv]
  dsimp only [A]
  field_simp [(hR.trans hr).ne'] <;> ring
