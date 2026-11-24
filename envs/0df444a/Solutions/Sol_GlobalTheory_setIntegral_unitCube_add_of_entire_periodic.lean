-- Prove2me | solution 1 for GlobalTheory.setIntegral_unitCube_add_of_entire_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:32:44.387544+00:00
-- url     : https://prove2.me/submissions/e6a6a1e0-7045-4d9a-8a6f-aeacc34d152a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ShiftSingleInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Theorems.Thm_GlobalTheory_setIntegral_unitCube_add_right_of_periodic
import Theorems.Thm_GlobalTheory_SCV_eq_of_invariant_real
import Theorems.Thm_GlobalTheory_differentiableOn_setIntegral_of_holomorphic_of_continuousOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {g : ℕ} {f : (Fin g → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (hper : ∀ (i : Fin g) z, f (z + Pi.single i 1) = f z)
    (w : Fin g → ℂ) :
    ∫ x in Set.Icc (0 : Fin g → ℝ) 1, f ((fun i => (x i : ℂ)) + w)
      = ∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) := by
  have hd : DifferentiableOn ℂ
      (fun w => ∫ x in Set.Icc (0 : Fin g → ℝ) 1, f ((fun i => (x i : ℂ)) + w)) Set.univ := by
    refine (differentiableOn_setIntegral_of_holomorphic_of_continuousOn
      (F := fun (x : Fin g → ℝ) w => f ((fun i => (x i : ℂ)) + w)) isOpen_univ
      isCompact_Icc subset_rfl measurableSet_Icc isCompact_Icc.measure_lt_top.ne ?_ ?_).1
    · have := hf.continuous
      refine Continuous.continuousOn ?_
      unfold Function.uncurry
      fun_prop
    · intro x _
      exact (hf.comp ((differentiable_const _).add differentiable_id)).differentiableOn
  have h := SCV.eq_of_invariant_real isOpen_univ isPreconnected_univ hd
    (fun z _ t _ => by
      have := setIntegral_unitCube_add_right_of_periodic
        (F := fun x : Fin g → ℝ => f ((fun i => (x i : ℂ)) + z)) (fun i x => by
          rw [← hper i ((fun i => (x i : ℂ)) + z)]
          congr 1
          funext j
          by_cases hij : j = i
          · subst hij; simp; ring
          · simp [hij]) t
      rw [← this]
      congr 1
      funext x
      congr 1
      funext j
      simp
      ring) (Set.mem_univ w) (Set.mem_univ 0)
  simpa using h
end GlobalTheory
