-- Prove2me | solution 1 for GlobalTheory.UnitaryOrbitForm.eq_zero_of_eventually_dotProduct_star_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:15:40.213098+00:00
-- url     : https://prove2.me/submissions/be8cc49e-1ff8-4490-b2c4-8a12cf0cab82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfEventuallyDotProductStarEqZero
import Theorems.Thm_GlobalTheory_UnitaryOrbitForm_eq_zero_of_forall_dotProduct_star_eq_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.UnitaryOrbitForm
open Matrix Filter Topology
variable {r : ℕ}
private lemma dotProduct_mulVec_star_add_smul_expand (C : Matrix (Fin r) (Fin r) ℂ) (a b : ℂ) (x y : Fin r → ℂ) :
    (a • x + b • y) ⬝ᵥ C *ᵥ star (a • x + b • y) =
      a * star a * (x ⬝ᵥ C *ᵥ star x) + b * star b * (y ⬝ᵥ C *ᵥ star y) +
        a * star b * (x ⬝ᵥ C *ᵥ star y) + b * star a * (y ⬝ᵥ C *ᵥ star x) := by
  simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring
end GlobalTheory.UnitaryOrbitForm
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitaryOrbitForm
open Matrix Filter Topology
variable {r : ℕ}
namespace GlobalTheory.UnitaryOrbitForm
theorem _root_.solution {C : Matrix (Fin r) (Fin r) ℂ}
    {v : Fin r → ℂ} (h : ∀ᶠ w in 𝓝 v, w ⬝ᵥ C *ᵥ star w = 0) : C = 0 := by
  apply eq_zero_of_forall_dotProduct_star_eq_zero
  intro u
  have hv : v ⬝ᵥ C *ᵥ star v = 0 := h.self_of_nhds
  have hc : ∀ s : ℝ, Continuous fun t : ℝ => (1 : ℂ) • v + ((s * t : ℝ) : ℂ) • u := fun s =>
    continuous_const.add ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).smul
      continuous_const)
  have e : ∀ s : ℝ, ∀ᶠ t : ℝ in 𝓝 0,
      ((1 : ℂ) • v + ((s * t : ℝ) : ℂ) • u) ⬝ᵥ C *ᵥ star ((1 : ℂ) • v + ((s * t : ℝ) : ℂ) • u) = 0 :=
    fun s => ((hc s).tendsto' 0 v (by simp)).eventually h
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ :=
    (((e 1).and (e (-1))).filter_mono nhdsWithin_le_nhds |>.and
      (self_mem_nhdsWithin : ({0}ᶜ : Set ℝ) ∈ 𝓝[≠] (0 : ℝ))).exists
  rw [dotProduct_mulVec_star_add_smul_expand, hv] at h1 h2
  simp only [star_one, Complex.star_def, Complex.conj_ofReal] at h1 h2
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have key : ((t : ℂ) ^ 2) * (u ⬝ᵥ C *ᵥ star u) = 0 := by
    push_cast at h1 h2
    linear_combination (h1 + h2) / 2
  exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 ht0)
end GlobalTheory.UnitaryOrbitForm
