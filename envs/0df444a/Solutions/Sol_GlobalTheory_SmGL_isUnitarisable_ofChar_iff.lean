-- Prove2me | solution 1 for GlobalTheory.SmGL.isUnitarisable_ofChar_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:54.984802+00:00
-- url     : https://prove2.me/submissions/9ef241f8-cd62-4668-a93b-3a53c1ff0642

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
variable {F G H V W U : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
namespace GlobalTheory.SmGL
theorem _root_.solution (χ : G →* ℂˣ) : IsUnitarisable (ofChar χ) ↔ IsUnitaryChar χ := by
  constructor
  · rintro ⟨B, -, hp, hi⟩ g
    have h := hi g 1 1
    have h0 : B 1 1 ≠ 0 := fun h => by simpa [h] using hp 1 one_ne_zero
    rw [ofChar_apply, ← smul_eq_mul, B.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
      smul_eq_mul, ← mul_assoc, Complex.mul_conj, mul_eq_right₀ h0] at h
    have h2 : ‖(χ g : ℂ)‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]; exact_mod_cast h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  · intro h
    refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => x * starRingEnd ℂ y)
      (fun _ _ _ => add_mul _ _ _) (fun _ _ _ => by simp [mul_assoc])
      (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp [mul_left_comm]), ?_, ?_, ?_⟩
    · intro v w; simp [mul_comm]
    · intro v hv; simpa [Complex.mul_conj] using hv
    · intro g v w
      have : (χ g : ℂ) * starRingEnd ℂ (χ g) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h g]; simp
      simp only [LinearMap.mk₂'ₛₗ_apply, ofChar_apply, map_mul]
      linear_combination (v * starRingEnd ℂ w) * this
end GlobalTheory.SmGL
