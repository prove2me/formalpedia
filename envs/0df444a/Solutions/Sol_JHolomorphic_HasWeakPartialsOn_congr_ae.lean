-- Prove2me | solution 1 for JHolomorphic.HasWeakPartialsOn.congr_ae
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T13:47:14.710987+00:00
-- url     : https://prove2.me/submissions/5fb2d3ac-abda-4e5b-938e-ca3ab72e983c

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp



namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

/-- Weak partial derivatives on `U` may be changed on null subsets of `U`, as may the map
itself. -/
theorem HasWeakPartialsOn.congr_ae_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℂ} (hU : IsOpen U) {u us ut u' us' ut' : ℂ → E} (h : HasWeakPartialsOn U u us ut)
    (hu : ∀ᵐ z ∂(volume.restrict U), u z = u' z) (hs : ∀ᵐ z ∂(volume.restrict U), us z = us' z)
    (ht : ∀ᵐ z ∂(volume.restrict U), ut z = ut' z) : HasWeakPartialsOn U u' us' ut' := by
  rw [ae_restrict_iff' hU.measurableSet] at hu hs ht
  intro φ hφ hφc hφU
  have hD : ∀ v : ℂ, ∀ z, z ∉ U → fderiv ℝ φ z v = 0 := fun v z hz => by
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h' => hz (hφU h'))]; simp
  have hV : ∀ z, z ∉ U → φ z = 0 := fun z hz =>
    Function.notMem_support.mp fun h' => hz (hφU (subset_tsupport _ h'))
  have hcong : ∀ (v : ℂ) (f f' : ℂ → E), (∀ᵐ z, z ∈ U → f z = f' z) →
      ∫ z, fderiv ℝ φ z v • f' z = ∫ z, fderiv ℝ φ z v • f z := fun v f f' hff' =>
    integral_congr_ae (hff'.mono fun z hz => by
      by_cases hzU : z ∈ U
      · simp [hz hzU]
      · simp [hD v z hzU])
  have hcong' : ∀ (f f' : ℂ → E), (∀ᵐ z, z ∈ U → f z = f' z) →
      ∫ z, φ z • f' z = ∫ z, φ z • f z := fun f f' hff' =>
    integral_congr_ae (hff'.mono fun z hz => by
      by_cases hzU : z ∈ U
      · simp [hz hzU]
      · simp [hV z hzU])
  obtain ⟨h1, h2⟩ := h φ hφ hφc hφU
  exact ⟨by rw [hcong 1 u u' hu, hcong' us us' hs, h1],
    by rw [hcong Complex.I u u' hu, hcong' ut ut' ht, h2]⟩

end JHolomorphic

open JHolomorphic JHolomorphic.HasWeakPartialsOn

open MeasureTheory Filter Topology
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℂ} (hU : IsOpen U) {u us ut u' us' ut' : ℂ → E} (h : HasWeakPartialsOn U u us ut)
    (hu : ∀ᵐ z ∂(volume.restrict U), u z = u' z) (hs : ∀ᵐ z ∂(volume.restrict U), us z = us' z)
    (ht : ∀ᵐ z ∂(volume.restrict U), ut z = ut' z) : HasWeakPartialsOn U u' us' ut' :=
  HasWeakPartialsOn.congr_ae_aux hU h hu hs ht
