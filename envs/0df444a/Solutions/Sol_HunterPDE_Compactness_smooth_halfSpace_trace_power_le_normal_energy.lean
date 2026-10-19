-- Prove2me | solution 1 for HunterPDE.Compactness.smooth_halfSpace_trace_power_le_normal_energy
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T13:50:43.718552+00:00
-- url     : https://prove2.me/submissions/70dc0354-d169-4917-93cc-9684215202db

import Theorems.Thm_HunterPDE_Compactness_smooth_halfSpace_trace_power_le_holder
import Theorems.Thm_HunterPDE_Compactness_holder_young_le_normal_energy
import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution {m : ℕ}
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : IsSmoothCompactClosedHalfSpace f) :
    eLpNorm (fun x' => f (boundaryPoint x')) p volume ^ p.toReal ≤
      ENNReal.ofReal p.toReal *
        (eLpNorm (HunterPDE.Shared.weakDeriv (upperHalfSpace m) 0 f)
            p (volume.restrict (upperHalfSpace m)) ^ p.toReal +
          eLpNorm (HunterPDE.Shared.weakDeriv (upperHalfSpace m)
            (Pi.single (Fin.last m) 1) f)
            p (volume.restrict (upperHalfSpace m)) ^ p.toReal) := by
  have hA := HunterPDE.Compactness.smooth_halfSpace_trace_power_le_holder (m := m) (p := p) hp hp' (f := f) hf
  have hB := HunterPDE.Compactness.holder_young_le_normal_energy (p := p) hp hp'
    (eLpNorm (HunterPDE.Shared.weakDeriv (upperHalfSpace m) 0 f) p (volume.restrict (upperHalfSpace m)) ^ p.toReal)
    (eLpNorm (HunterPDE.Shared.weakDeriv (upperHalfSpace m) (Pi.single (Fin.last m) 1) f)
      p (volume.restrict (upperHalfSpace m)) ^ p.toReal)
  exact le_trans hA hB
