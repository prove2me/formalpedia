-- Prove2me | solution 1 for GlobalTheory.JR.SuppBdd.pow_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:12:52.088807+00:00
-- url     : https://prove2.me/submissions/71b15ad6-cbc0-4749-8ab3-78170529ac88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactUnitariesIntegralOrbitOfHankelDetNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SuppBdd
namespace GlobalTheory.JR.SuppBdd
theorem _root_.solution {n : ℕ} {E : Type} [CommRing E] [StarRing E] (g : Matrix.unitaryGroup (Fin n) E)
    (A : Matrix (Fin n) (Fin n) E) (j : ℕ) : (g.1 * A * star g.1) ^ j = g.1 * A ^ j * star g.1 := by
  have hg : star g.1 * g.1 = 1 := Unitary.star_mul_self_of_mem g.2
  have hg' : g.1 * star g.1 = 1 := Unitary.mul_star_self_of_mem g.2
  induction j with
  | zero => simp [hg']
  | succ j ih =>
    rw [pow_succ, ih, pow_succ]
    calc g.1 * A ^ j * star g.1 * (g.1 * A * star g.1) = g.1 * A ^ j * (star g.1 * g.1) * A * star g.1 := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg, Matrix.mul_one]; simp only [Matrix.mul_assoc]
end GlobalTheory.JR.SuppBdd
