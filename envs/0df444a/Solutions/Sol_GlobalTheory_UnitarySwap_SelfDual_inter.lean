-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.SelfDual.inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:15:42.580266+00:00
-- url     : https://prove2.me/submissions/eb52fd1b-7ceb-402b-bd00-fbf2ef4bef3c

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_pair
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_perp
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
namespace SelfDual
theorem _root_.solution (h : SelfDual B W Λ) (hB : ∀ u v, σ (B u v) = B v u) {e f x y : V}
    (hx : ∀ v, B e v = 0 → B x v = 0) (hy : ∀ v, B f v = 0 → B y v = 0)
    (hdec : ∀ v ∈ Λ, ∃ c ∈ intL L, ∃ d ∈ intL L, ∃ v₀ ∈ Λ,
      B e v₀ = 0 ∧ B f v₀ = 0 ∧ v = c • x + d • y + v₀) :
    SelfDual B (perp B W e f) (Λ ∩ (perp B W e f : Set V)) := by
  intro v
  constructor
  · rintro ⟨hv, hv'⟩
    exact ⟨hv', fun w hw => h.pair hv hw.1⟩
  · rintro ⟨hv, hv'⟩
    refine ⟨(h v).2 ⟨(mem_perp.1 hv).1, fun w hw => ?_⟩, hv⟩
    obtain ⟨c, -, d, -, w₀, hw₀, h1, h2, rfl⟩ := hdec w hw
    have e1 : B v x = 0 := by rw [← hB, hx v (mem_perp.1 hv).2.1, map_zero]
    have e2 : B v y = 0 := by rw [← hB, hy v (mem_perp.1 hv).2.2, map_zero]
    simp only [map_add, map_smul, e1, e2, smul_zero, zero_add]
    exact hv' w₀ ⟨hw₀, mem_perp.2 ⟨((h w₀).1 hw₀).1, h1, h2⟩⟩
end SelfDual
end GlobalTheory.UnitarySwap
