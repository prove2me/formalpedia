-- Prove2me | solution 1 for MinVolEllipsoid.containment_iff_Z_le_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:10:43.547179+00:00
-- url     : https://prove2.me/submissions/45a2a598-adc9-4f04-b468-6c45f255835c

import Mathlib
import Definitions.Def_MinVolEllipsoid_Zval
import Definitions.Def_ConvexOptimization_ellipsoidBody

open Matrix

open MinVolEllipsoid in
theorem solution {n : ℕ} (P : Set (Fin n → ℝ)) (hPc : IsCompact P)
    (hPcv : Convex ℝ P) (hPi : (interior P).Nonempty) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (b : Fin n → ℝ) :
    P ⊆ ConvexOptimization.ellipsoidBody A b ↔ Zval P A b ≤ 1 := by
  have hf : Continuous (fun x : Fin n → ℝ => (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b)) := by
    simp only [dotProduct, Matrix.mulVec, Pi.add_apply]
    fun_prop
  have hne : P.Nonempty := hPi.mono interior_subset
  have hbdd := (hPc.image hf).bddAbove
  unfold Zval
  rw [csSup_le_iff hbdd (hne.image _), Set.forall_mem_image]
  rfl
