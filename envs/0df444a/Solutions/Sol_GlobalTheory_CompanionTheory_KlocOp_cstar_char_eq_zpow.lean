-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KlocOp.cstar_char_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:00:54.1678+00:00
-- url     : https://prove2.me/submissions/185090aa-a297-468d-869b-b27786f8e41b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousUnitaryMultiplicativeEqArgPow
import Theorems.Thm_GroundTheory_Global_coe_circleToUnits
import Theorems.Thm_GroundTheory_Global_existsUnique_complexUnits_circle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.coe_circleToUnits



set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KlocOp
namespace GlobalTheory.CompanionTheory.KlocOp
theorem _root_.solution : ∀ φ : ℂ → ℂ, (∀ z w : ℂ, z ≠ 0 → w ≠ 0 → φ (z * w) = φ z * φ w) →
    ContinuousOn φ {z : ℂ | z ≠ 0} → (∀ z : ℂ, z ≠ 0 → ‖φ z‖ = 1) →
    (∀ r : ℝ, 0 < r → φ (r : ℂ) = 1) →
    ∃ k : ℤ, ∀ z : ℂ, z ≠ 0 → φ z = (z / (‖z‖ : ℂ)) ^ k := by
  intro φ hmul hc hn h1
  have hmem : ∀ z : ℂˣ, φ (z : ℂ) ∈ Submonoid.unitSphere ℂ := fun z => by
    simpa [Submonoid.unitSphere] using hn z z.ne_zero
  let f : ℂˣ → Circle := fun z => ⟨φ (z : ℂ), hmem z⟩
  have hfc : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact hc.comp_continuous Units.continuous_val fun z => z.ne_zero
  have hf1 : f 1 = 1 := by
    apply Circle.ext
    have := h1 1 one_pos
    simpa [f] using this
  have hfm : ∀ a b : ℂˣ, f (a * b) = f a * f b := fun a b => by
    apply Circle.ext
    rw [Circle.coe_mul]
    change φ ((a * b : ℂˣ) : ℂ) = φ (a : ℂ) * φ (b : ℂ)
    rw [Units.val_mul]
    exact hmul a b a.ne_zero b.ne_zero
  let χ : ℂˣ →ₜ* Circle :=
    { toFun := f, map_one' := hf1, map_mul' := hfm, continuous_toFun := hfc }
  obtain ⟨⟨m, τ⟩, hp, -⟩ := GroundTheory.Global.existsUnique_complexUnits_circle χ
  have hp' : ∀ z : ℂˣ, φ (z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ m *
      ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) := hp
  have hr : ∀ r : ℝ, 0 < r → (r : ℂ) ^ ((τ : ℂ) * Complex.I) = 1 := by
    intro r hr0
    have hne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have h := hp' (Units.mk0 (r : ℂ) hne)
    rw [Units.val_mk0, h1 r hr0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      div_self hne, one_zpow, one_mul] at h
    exact h.symm
  refine ⟨m, fun z hz => ?_⟩
  have h := hp' (Units.mk0 z hz)
  rw [Units.val_mk0, hr _ (norm_pos_iff.mpr hz), mul_one] at h
  exact h
end GlobalTheory.CompanionTheory.KlocOp
