-- Prove2me | solution 1 for GlobalTheory.BorelUMod.smul_mem_upLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:53.781853+00:00
-- url     : https://prove2.me/submissions/8fe76743-5d73-4bf6-ad75-46c8da187fa9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open GlobalTheory.LGrp Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.BorelUMod
namespace _root_.GlobalTheory.BorelUMod
theorem _root_.solution {c : Fin n → Fin n → ℤ} {a : L}
    (ha : Valued.v a ≤ 1) {X : Matrix (Fin n) (Fin n) L}
    (hX : X ∈ _root_.GlobalTheory.BorelUMod.upLat L c) : a • X ∈ _root_.GlobalTheory.BorelUMod.upLat L c := by
  refine ⟨fun i j hji => by simp [hX.1 i j hji], fun i j hij => ?_⟩
  rw [Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]
  calc Valued.v a * Valued.v (X i j) ≤ 1 * WithZero.exp (-c i j) := mul_le_mul' ha (hX.2 i j hij)
    _ = WithZero.exp (-c i j) := one_mul _
end _root_.GlobalTheory.BorelUMod
end GlobalTheory.BorelUMod
