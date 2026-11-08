-- Prove2me | solution 1 for KnillLaflammeQEC.isKrausFamily_of_projections
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:50:31.588743+00:00
-- url     : https://prove2.me/submissions/497fe1b3-bbbb-43de-a1b4-987a58c02254

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
open scoped Matrix

theorem solution {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]
    (P : K → Matrix ι ι ℂ) (hP : ∀ r, (P r)ᴴ = P r ∧ P r * P r = P r) (hsum : ∑ r, P r = 1)
    (W : K → Matrix.unitaryGroup ι ℂ) :
    QAlgorithms.IsKrausFamily (fun r => (W r : Matrix ι ι ℂ) * P r) := by
  unfold QAlgorithms.IsKrausFamily
  rw [← hsum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have hW : star (W r : Matrix ι ι ℂ) * (W r : Matrix ι ι ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (W r).2
  rw [Matrix.star_eq_conjTranspose] at hW
  rw [Matrix.conjTranspose_mul, (hP r).1, Matrix.mul_assoc, ← Matrix.mul_assoc _ (W r : Matrix ι ι ℂ),
    hW, Matrix.one_mul, (hP r).2]
