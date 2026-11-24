-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.SelfDual.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:55:24.059477+00:00
-- url     : https://prove2.me/submissions/8ba0776a-482f-418b-89cd-907ad44ba424

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {V : Type} [AddCommGroup V] [Module L V] {σ : L →+* L}
variable {B : V →ₛₗ[σ] V →ₗ[L] L} {W : Submodule L V} {Λ : Set V}
namespace GlobalTheory.UnitarySwap
namespace SelfDual
theorem _root_.solution (h : SelfDual B W Λ) (hσ : ∀ x ∈ intL L, σ x ∈ intL L) {c : L} (hc : c ∈ intL L)
    {v : V} (hv : v ∈ Λ) : c • v ∈ Λ := by
  rw [h] at hv ⊢
  refine ⟨W.smul_mem c hv.1, fun w hw => ?_⟩
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  exact mul_mem (hσ c hc) (hv.2 w hw)
end SelfDual
end GlobalTheory.UnitarySwap
