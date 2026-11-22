-- Prove2me | solution 2 for NoHair.israel_static_electrovac
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:58:23.661796+00:00
-- url     : https://prove2.me/submissions/38851531-b2b0-4aa3-b97a-232f0f3ad022
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_static_electrovac_areal_reduction
import Theorems.Thm_NoHair_radial_electrovac_exterior_parameters

open scoped ContDiff Manifold BigOperators
open Set NoHair

private lemma field_scales_with_charge (e : ℝ) (y : E4) :
    kerrNewmanField 0 e y = e • kerrNewmanField 0 1 y := by
  have hpot (j : Fin 4) : (fun z : E4 => kerrNewmanPotential 0 e z j) =
      e • (fun z : E4 => kerrNewmanPotential 0 1 z j) := by
    funext z
    simp only [kerrNewmanPotential, Pi.smul_apply, smul_eq_mul, one_mul]
    ring
  ext i j
  simp only [kerrNewmanField, coordPartial, hpot, fderiv_const_smul_field,
    Matrix.smul_apply, Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private lemma hodgeDual_smul_field (G F : Matrix (Fin 4) (Fin 4) ℝ) (c : ℝ) :
    hodgeDual G (c • F) = c • hodgeDual G F := by
  let raised (A : Matrix (Fin 4) (Fin 4) ℝ) (k l : Fin 4) :=
    ∑ i, ∑ j, G⁻¹ k i * G⁻¹ l j * A i j
  have hraised (k l : Fin 4) : raised (c • F) k l = c * raised F k l := by
    simp only [raised, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  ext i j
  have hsum : (∑ k, ∑ l, leviCivita i j k l * raised (c • F) k l) =
      c * ∑ k, ∑ l, leviCivita i j k l * raised F k l := by
    simp only [hraised, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
  change (1 / 2 : ℝ) * Real.sqrt |G.det| * (∑ k, ∑ l, leviCivita i j k l * raised (c • F) k l) =
    c * ((1 / 2 : ℝ) * Real.sqrt |G.det| * ∑ k, ∑ l, leviCivita i j k l * raised F k l)
  rw [hsum]
  ring

private lemma metric_of_mass_profile (m e μ : ℝ) (y : E4) (hr : 0 < ksRadius 0 y)
    (hμ : μ = m - e ^ 2 / (2 * ksRadius 0 y)) :
    kerrNewmanMetric μ 0 0 y = kerrNewmanMetric m 0 e y := by
  have hprofile : ksProfile μ 0 0 y = ksProfile m 0 e y := by
    rw [hμ]
    simp only [ksProfile, zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero, add_zero]
    field_simp [hr.ne'] <;> ring
  ext i j
  simp only [kerrNewmanMetric, hprofile]

theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hstatic : IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ m e : ℝ, IsKerrNewmanBlackHoleParams m 0 e ∧
      IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m 0 e := by
  obtain ⟨R, μ, u, v, ψ, hR, hcont, horizon, exterior, electric, magnetic, mass, hψ, hmatch⟩ :=
    static_electrovac_areal_reduction g F T φ E h hstatic
  obtain ⟨m, e, β, _, hadm, hradius, hprofiles⟩ :=
    radial_electrovac_exterior_parameters R μ u v hR hcont horizon exterior electric magnetic mass
  refine ⟨m, e, hadm, β, ψ, ?_, ?_⟩
  · simpa only [kerrNewmanDOC, hradius] using hψ
  · intro y hy
    have hr : R < ksRadius 0 y := by
      simpa only [kerrNewmanDOC, Set.mem_setOf_eq, hradius] using hy
    obtain ⟨hμ, hu, hv⟩ := hprofiles _ hr
    obtain ⟨hg, hF⟩ := hmatch y hr
    have hmetric := metric_of_mass_profile m e _ y (hR.trans hr) hμ
    refine ⟨hg.trans hmetric, ?_⟩
    rw [hF, hmetric, hu, hv, field_scales_with_charge e y, hodgeDual_smul_field]
    simp only [smul_smul]
