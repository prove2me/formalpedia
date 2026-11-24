-- Prove2me | solution 1 for GlobalTheory.BK.E_mul_N_Ezpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:34:13.489798+00:00
-- url     : https://prove2.me/submissions/c26f9dbe-2afe-4725-9fae-9d7fdf93d209

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Theorems.Thm_GlobalTheory_BK_Ezpow_add
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.Hom.onPol_cls
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) {a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
omit [IsUltrametricDist K]
namespace GlobalTheory.BK
theorem _root_.solution (j : ℤ) :
    E K l e * N K (Ezpow K l e j) = (j : K⟦X⟧) * N K (E K l e) * Ezpow K l e j := by
  have key (i : ℤ) : N K (Ezpow K l e (i + 1)) =
      Ezpow K l e i * N K (E K l e) + E K l e * N K (Ezpow K l e i) := by
    rw [Ezpow_add, show Ezpow K l e 1 = E K l e from (Ezpow_natCast l e 1).trans (pow_one _),
      Derivation.leibniz]
    rfl
  have h1 (i : ℤ) : Ezpow K l e (i + 1) = Ezpow K l e i * E K l e := by
    rw [Ezpow_add, show Ezpow K l e 1 = E K l e from (Ezpow_natCast l e 1).trans (pow_one _)]
  induction j using Int.induction_on with
  | zero => simp [Ezpow]
  | succ i ih =>
    rw [key, ih, h1]
    push_cast
    ring
  | pred i ih =>
    have h := key (-i - 1)
    have h' := h1 (-i - 1)
    rw [sub_add_cancel] at h h'
    rw [h, h'] at ih
    refine (isUnit_E (K := K) l e).mul_left_cancel ?_
    push_cast at ih ⊢
    linear_combination ih
end GlobalTheory.BK
