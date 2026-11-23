-- Prove2me | solution 1 for NoHair.schwarzschild_of_positive_harmonic_double
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T07:02:35.966454+00:00
-- url     : https://prove2.me/submissions/1eb0abae-28f6-4291-887b-185ed66b2b30

import Theorems.Thm_NoHair_positive_punctured_harmonic_monopole
import Theorems.Thm_NoHair_schwarzschild_isotropic_exterior_change
open NoHair Set InnerProductSpace
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

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M]
    (g F : BilinField M) (D : Set M) (hF : ∀ x ∈ D, F x = 0)
    (U : EuclideanSpace ℝ (Fin 3) → ℝ) (hchart : HasConformalVacuumExterior g D U)
    (hh : HarmonicOnNhd U ({0}ᶜ)) (hpos : ∀ x, x ≠ 0 → 0 ≤ U x)
    (hfar : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |U x - 1| ≤ ε)
    (p : EuclideanSpace ℝ (Fin 3)) (hp : p ≠ 0) (hlevel : U p = 2) :
    0 < 2 * ‖p‖ ∧ IsKerrNewmanDOC g F D (2 * ‖p‖) 0 0 := by
  obtain ⟨b,hb₀,hV⟩ := positive_punctured_harmonic_monopole U hh hpos hfar
  have nn : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have bp : b = ‖p‖ := by
    have e := hV p hp
    rw [hlevel] at e
    have f : b / ‖p‖ = 1 := by linarith
    simpa using (div_eq_iff nn.ne').mp f
  subst b
  have hb := nn
  obtain ⟨ho,ψ,hψ,hmetric⟩ := hchart
  let V := fun x : EuclideanSpace ℝ (Fin 3) => 1 + ‖p‖ / ‖x‖
  have hdom : conformalExteriorDomain U = conformalExteriorDomain V := by
    ext z
    change (_ ≠ 0 ∧ U _ < 2) ↔ (_ ≠ 0 ∧ V _ < 2)
    constructor <;> rintro ⟨hz, hlt⟩ <;> exact ⟨hz, by simpa only [hV _ hz, V] using hlt⟩
  rw [hdom] at hψ hmetric
  obtain ⟨H, hH, hHM⟩ := schwarzschild_isotropic_exterior_change ‖p‖ hb
  have hchart := compose_charts hH hψ
  let m := 2 * ‖p‖
  let R := 4 * ‖p‖
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
    rw [positive_side ‖p‖ hb]
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
  refine ⟨hm,0,ψ ∘ H,hchart,?_⟩
  intro y hy
  have hy' : R<ksRadius 0 y := by rwa [harea] at hy
  refine ⟨pulled y hy',?_⟩
  have zeroF := hF _ (hchart.choose_spec.1 hy)
  change F (ψ (H y)) = 0 at zeroF
  ext i j
  simp [pullbackCoeffs,zeroF,kerrNewmanField,kerrNewmanPotential,coordPartial]
