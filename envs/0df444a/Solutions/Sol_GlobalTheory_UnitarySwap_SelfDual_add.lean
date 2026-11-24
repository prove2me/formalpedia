-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.SelfDual.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:15:22.709803+00:00
-- url     : https://prove2.me/submissions/5a7ad62f-99c6-483b-8397-8ac14300f108

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
theorem _root_.solution (h : SelfDual B W Λ) {u v : V} (hu : u ∈ Λ) (hv : v ∈ Λ) : u + v ∈ Λ := by
  rw [h] at hu hv ⊢
  refine ⟨W.add_mem hu.1 hv.1, fun w hw => ?_⟩
  rw [map_add, LinearMap.add_apply]
  exact add_mem (hu.2 w hw) (hv.2 w hw)
end SelfDual
end GlobalTheory.UnitarySwap
