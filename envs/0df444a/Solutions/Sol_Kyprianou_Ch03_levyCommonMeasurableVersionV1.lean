-- Prove2me | solution 1 for Kyprianou.Ch03.levyCommonMeasurableVersionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:45:39.042853+00:00
-- url     : https://prove2.me/submissions/a3300abf-4ad4-4514-8897-76d75e70be84

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P) :
    ∃ Y : NNReal → Omega → ℝ, IsLevyProcess Y P ∧
      (∀ t, Measurable (Y t)) ∧ (∀ᵐ w ∂P, ∀ t, Y t w = X t w) := by
  classical
  let W : Omega → (NNReal → ℝ) := fun w t => X t w
  have hW : AEMeasurable W P :=
    Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 P X hX
  let Y (t : NNReal) (w : Omega) := if t = 0 then 0 else hW.mk W w t
  have hEq : ∀ᵐ w ∂P, ∀ t, Y t w = X t w := by
    filter_upwards [hW.ae_eq_mk] with w hw
    intro t
    by_cases ht : t = 0
    · subst t
      simp [Y, hX.start_zero]
    · simpa [Y, ht, W] using (congrFun hw t).symm
  have hMeas (t : NNReal) : Measurable (Y t) := by
    by_cases ht : t = 0
    · simp [Y, ht]
    · simpa [Y, ht, Function.comp_def] using (measurable_pi_apply t).comp hW.measurable_mk
  have hinc (s t : NNReal) : ProbabilityTheory.increment Y s t =ᵐ[P]
      ProbabilityTheory.increment X s t := by
    filter_upwards [hEq] with w hw
    simp [ProbabilityTheory.increment, hw]
  refine ⟨Y, ⟨by funext w; simp [Y], ?_, ?_, ?_⟩, hMeas, hEq⟩
  · intro n ts ht
    exact (iIndepFun_congr (fun k : Fin n => hinc (ts k.castSucc) (ts k.succ))).mpr
      (hX.indep_increments n ts ht)
  · intro s h
    have hi (a b : NNReal) : IdentDistrib (ProbabilityTheory.increment Y a b)
        (ProbabilityTheory.increment X a b) P P :=
      IdentDistrib.of_ae_eq ((hMeas b).sub (hMeas a)).aemeasurable (hinc a b)
    exact ((hi s (s+h)).trans (hX.stationary_increments s h)).trans (hi 0 h).symm
  · filter_upwards [hEq, hX.cadlag_ae] with w hw hc
    rw [show (fun t => Y t w) = (fun t => X t w) from funext hw]
    exact hc
