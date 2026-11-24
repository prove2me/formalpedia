-- Prove2me | solution 1 for GlobalTheory.BruhatRep.rho_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:04:00.261916+00:00
-- url     : https://prove2.me/submissions/a14517dd-c11a-4122-9edc-60fbd49b97fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
import Theorems.Thm_GlobalTheory_BruhatRep_mx_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.BruhatRep
variable {K : Type} [Field K]
variable {M : Type} [Monoid M]
variable (n : K → M) (m : Kˣ → M) (t : M)
namespace GlobalTheory.BruhatRep
theorem _root_.solution (hn0 : n 0 = 1) (hm1 : m 1 = 1) : rho n m t (1 : SpecialLinearGroup (Fin 2) K) = 1 := by
  have e : ∀ i j : Fin 2, en (1 : SpecialLinearGroup (Fin 2) K) i j = (1 : Matrix (Fin 2) (Fin 2) K) i j :=
    fun _ _ => rfl
  simp only [rho, e, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.one_apply_eq, if_true, zero_div, hn0, mul_one]
  have := mx_unit m 1; rw [Units.val_one] at this; rw [this, hm1]
end GlobalTheory.BruhatRep
