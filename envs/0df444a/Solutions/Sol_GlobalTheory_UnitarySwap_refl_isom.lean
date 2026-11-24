-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.refl_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:10:02.577366+00:00
-- url     : https://prove2.me/submissions/30f8e30c-9cd1-4cc9-a64c-4ac6e0493837

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_GlobalTheory_UnitarySwap_refl_apply
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
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {V : Type} [AddCommGroup V] [Module L V] {σ : L →+* L}
variable {B : V →ₛₗ[σ] V →ₗ[L] L} {W : Submodule L V} {Λ : Set V}
namespace GlobalTheory.UnitarySwap
theorem _root_.solution (hB : ∀ u v, σ (B u v) = B v u) (w : V) (μ : L) (hμ : μ ≠ 0)
    (hw : B w w = μ + σ μ) (u v : V) : B (refl B w μ u) (refl B w μ v) = B u v := by
  have hμ' : σ μ ≠ 0 := (map_ne_zero σ).2 hμ
  simp only [refl_apply, map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, map_mul, map_inv₀, hB, hw, RingHom.id_apply]
  field_simp
  ring
end GlobalTheory.UnitarySwap
