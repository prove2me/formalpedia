-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Interlacing.lagrangeFactor_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/0731b05e-bfc2-42e4-8306-c89248279582

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHierarchy
namespace Interlacing
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (ℓ : Fin (r + 1)) (m : Fin r) :
    0 < (quadraticCoordinate (a ℓ) - quadraticCoordinate (b m)) /
      (quadraticCoordinate (a ℓ) -
        quadraticCoordinate (a (ℓ.succAbove m))) := by
  by_cases hm : m.castSucc < ℓ
  · rw [Fin.succAbove_of_castSucc_lt ℓ m hm]
    have hmiddle : a ℓ < b m := by
      exact
        (h.strictAnti_ambient.antitone (Fin.castSucc_lt_iff_succ_le.mp hm)).trans_lt
          (h.2 m).2
    have hleft :
        quadraticCoordinate (a ℓ) < quadraticCoordinate (b m) :=
      quadraticCoordinate_strictMonoOn (h.ambient_nonneg ℓ)
        (h.stabilizer_pos m).le hmiddle
    have hright :
        quadraticCoordinate (a ℓ) <
          quadraticCoordinate (a m.castSucc) :=
      quadraticCoordinate_strictMonoOn (h.ambient_nonneg ℓ)
        (h.ambient_nonneg m.castSucc) (h.strictAnti_ambient hm)
    exact div_pos_of_neg_of_neg (sub_neg.mpr hleft) (sub_neg.mpr hright)
  · have hm' : ℓ ≤ m.castSucc := le_of_not_gt hm
    rw [Fin.succAbove_of_le_castSucc ℓ m hm']
    have hmiddle : b m < a ℓ := by
      exact (h.2 m).1.trans_le (h.strictAnti_ambient.antitone hm')
    have hleft :
        quadraticCoordinate (b m) < quadraticCoordinate (a ℓ) :=
      quadraticCoordinate_strictMonoOn (h.stabilizer_pos m).le
        (h.ambient_nonneg ℓ) hmiddle
    have hright :
        quadraticCoordinate (a m.succ) < quadraticCoordinate (a ℓ) :=
      quadraticCoordinate_strictMonoOn (h.ambient_nonneg m.succ)
        (h.ambient_nonneg ℓ)
        (h.strictAnti_ambient (Fin.le_castSucc_iff.mp hm'))
    exact div_pos (sub_pos.mpr hleft) (sub_pos.mpr hright)
end Interlacing
end MetricCodes.Spherical.HigherHierarchy
