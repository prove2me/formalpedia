-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.selfDual_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:33:10.782802+00:00
-- url     : https://prove2.me/submissions/baf9cbd2-b240-4594-857c-8c52470f211c

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_pair
import Theorems.Thm_GlobalTheory_UnitarySwap_form_mulVec
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
variable {n : ℕ} {σ : L →+* L}
namespace GlobalTheory.UnitarySwap
theorem _root_.solution {J : Matrix (Fin n) (Fin n) L} {Λ : Set (Fin n → L)}
    (h : SelfDual (form σ J) ⊤ Λ) {g : GL (Fin n) L} (hg : g ∈ UJ σ J) :
    SelfDual (form σ J) ⊤ {v | (g : Matrix (Fin n) (Fin n) L) *ᵥ v ∈ Λ} := by
  have hg' : ∀ u v, form σ J ((g : Matrix (Fin n) (Fin n) L) *ᵥ u) ((g : Matrix (Fin n) (Fin n) L) *ᵥ v)
      = form σ J u v := fun u v => by rw [form_mulVec, show _ = J from hg]
  intro v
  constructor
  · intro hv
    exact ⟨trivial, fun w hw => by rw [← hg']; exact h.pair hv hw⟩
  · rintro ⟨-, hv⟩
    refine (h _).2 ⟨trivial, fun w hw => ?_⟩
    have e : (g : Matrix (Fin n) (Fin n) L) *ᵥ (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [← e, hg']
    exact hv _ (by show _ ∈ Λ; rw [e]; exact hw)
end GlobalTheory.UnitarySwap
