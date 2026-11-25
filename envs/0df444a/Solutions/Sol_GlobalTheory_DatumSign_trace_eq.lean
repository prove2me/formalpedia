-- Prove2me | solution 1 for GlobalTheory.DatumSign.trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:38:08.007776+00:00
-- url     : https://prove2.me/submissions/5c95e692-613a-47e9-a101-c5286eda83ad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_PEqQOfNeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DatumSign
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Module
open scoped TensorProduct
variable {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
namespace GlobalTheory.DatumSign
namespace _root_.GlobalTheory.DatumSign
theorem _root_.solution :
    ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V) (s : ℝ),
      ∀ (hs : (0 : ℝ) < s) (hT : ∀ (x : V), T (T x) = (s * s) • x),
        LinearMap.trace ℝ V T =
          s * ((2 : ℝ) * (Module.finrank ℝ (T - s • LinearMap.id).ker : ℝ) -
            (Module.finrank ℝ V : ℝ)) := by
  intro V _ _ _ T s hs hT
  set P : V →ₗ[ℝ] V := (2 * s)⁻¹ • (T + s • LinearMap.id) with hP
  have hproj : LinearMap.IsProj (T - s • LinearMap.id).ker P := by
    constructor
    · intro x
      simp only [LinearMap.mem_ker, hP, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.add_apply, LinearMap.id_apply, map_smul, map_add, hT]
      rw [smul_sub s (T x), smul_smul, sub_add_sub_cancel, sub_self, smul_zero]
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
      simp only [hP, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, hx,
        ← two_smul ℝ (s • x), smul_smul]
      rw [show (2 * s)⁻¹ * (2 * s) = 1 by field_simp, one_smul]
  have htr := hproj.trace
  have hTP : T = (2 * s) • P - s • LinearMap.id := by
    rw [hP, smul_smul, mul_inv_cancel₀ (by positivity), one_smul, add_sub_cancel_right]
  clear_value P
  conv_lhs => rw [hTP]
  rw [map_sub, map_smul, map_smul, htr, LinearMap.trace_id, smul_eq_mul, smul_eq_mul]
  ring
end _root_.GlobalTheory.DatumSign
end GlobalTheory.DatumSign
