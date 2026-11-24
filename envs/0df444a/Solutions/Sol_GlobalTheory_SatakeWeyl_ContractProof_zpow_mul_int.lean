-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.ContractProof.zpow_mul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:31:32.235628+00:00
-- url     : https://prove2.me/submissions/c9f1a941-c4f7-4e9e-ab68-65c1340466f4

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryDominantDiagonalConjugationContracts
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
noncomputable section
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.ContractProof
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}
namespace GlobalTheory.SatakeWeyl.ContractProof
theorem _root_.solution {ϖ : L} (hv : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (x : L) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ m → ϖ ^ m * x ∈ intL L := by
  by_cases hx : x = 0
  · exact ⟨0, fun m _ => by rw [hx, mul_zero]; exact zero_mem _⟩
  have hx' : Valued.v x ≠ (0 : WithZero (Multiplicative ℤ)) := by simpa using hx
  refine ⟨(WithZero.log (Valued.v x : WithZero (Multiplicative ℤ))).toNat, fun m hm => ?_⟩
  show Valued.v (ϖ ^ m * x) ≤ (1 : WithZero (Multiplicative ℤ))
  rw [map_mul, map_zpow₀, hv, ← WithZero.exp_log hx', ← WithZero.exp_zsmul, ← WithZero.exp_add,
    ← WithZero.exp_zero, WithZero.exp_le_exp]
  have := Int.self_le_toNat (WithZero.log (Valued.v x : WithZero (Multiplicative ℤ)))
  simp only [smul_eq_mul]
  omega
end GlobalTheory.SatakeWeyl.ContractProof
