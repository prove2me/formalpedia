-- Prove2me | solution 1 for GlobalTheory.CofactorOrder.exists_coeff_adjugate_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:29:57.639288+00:00
-- url     : https://prove2.me/submissions/94914ac2-b55f-4aa2-bdbc-d7c7d5ffc796

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotXPowDvdAdjugateOfFirstOrderKernel
import Theorems.Thm_GlobalTheory_CofactorOrder_adjugate_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory
open GlobalTheory.CofactorOrder
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CofactorOrder
theorem _root_.solution [Nonempty n] (Ψ : Matrix n n K[X])
    (h : Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ 1) :
    ∃ b c, ¬ (X : K[X]) ∣ Ψ.adjugate b c := by
  have hmap : (Ψ.map fun p => p.coeff 0) = constantCoeff.mapMatrix Ψ := by
    ext i j
    simp [constantCoeff_apply]
  have hne := adjugate_ne_zero _ h
  rw [hmap, ← RingHom.map_adjugate] at hne
  by_contra hall
  push Not at hall
  apply hne
  ext b c
  rw [RingHom.mapMatrix_apply, map_apply, Matrix.zero_apply, constantCoeff_apply]
  exact X_dvd_iff.mp (hall b c)
end GlobalTheory.CofactorOrder
