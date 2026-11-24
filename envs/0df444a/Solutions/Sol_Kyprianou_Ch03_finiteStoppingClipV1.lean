-- Prove2me | solution 1 for Kyprianou.Ch03.finiteStoppingClipV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:24:29.357902+00:00
-- url     : https://prove2.me/submissions/e220f35c-2e6f-4c21-aece-9071f7fc2492

import Mathlib
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration

open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (r : Omega → NNReal)
    (hr : ∀ w, tau w ≠ ⊤ → tau w = (r w : WithTop NNReal))
    (s : NNReal) :
    ∃ rho : Omega → NNReal,
      IsStoppingTime F (fun w => (rho w : WithTop NNReal)) ∧
      (∀ w, rho w ≤ s) ∧
      (∀ w, tau w ≤ (s : WithTop NNReal) → rho w = r w) := by
  classical
  have hex (w : Omega) : ∃ v : NNReal, (v : WithTop NNReal) =
      min (tau w) (s : WithTop NNReal) :=
    WithTop.ne_top_iff_exists.mp
      (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _))
  choose rho he using hex
  refine ⟨rho, ?_, ?_, ?_⟩
  · simpa only [he] using hTau.min_const s
  · intro w
    exact WithTop.coe_le_coe.mp (by rw [he]; exact min_le_right _ _)
  · intro w hw
    apply WithTop.coe_injective
    rw [he,min_eq_left hw,hr w (ne_top_of_le_ne_top WithTop.coe_ne_top hw)]
