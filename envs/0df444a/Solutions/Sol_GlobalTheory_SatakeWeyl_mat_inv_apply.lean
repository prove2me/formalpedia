-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.mat_inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:54:09.300604+00:00
-- url     : https://prove2.me/submissions/4693543c-2417-4a3c-9da3-264e524a940b

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_mul_inv
import Theorems.Thm_GlobalTheory_SatakeWeyl_antiJ_mul_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_fSatake_cTJ
import Theorems.Thm_GlobalTheory_UnitarySwap_antiJ_mul_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism.UG
open GlobalTheory GlobalTheory.SatakeWeyl
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution (g : GU σ n) (i j : Fin n) : mat g⁻¹ i j = σ (mat g j.rev i.rev) := by
  have h1 : cT σ (mat g) * antiJ L n * mat g = antiJ L n := g.2
  have h2 : mat g⁻¹ = antiJ L n * (cT σ (mat g) * antiJ L n) := by
    calc mat g⁻¹ = antiJ L n * (cT σ (mat g) * antiJ L n * mat g) * mat g⁻¹ := by
          rw [h1, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]
  rw [h2, antiJ_mul_apply, P.fSatake_cTJ]
end GlobalTheory.SatakeWeyl
