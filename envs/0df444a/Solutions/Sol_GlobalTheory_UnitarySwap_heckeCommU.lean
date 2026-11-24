-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.heckeCommU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:51:25.515415+00:00
-- url     : https://prove2.me/submissions/09edc2b8-62b3-461c-9bb0-20903f5e927d

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_GlobalTheory_UnitarySwap_inv_mem_doubleCoset
import Theorems.Thm_GlobalTheory_UnitarySwap_antiJ_mul_self
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_cartan_exists_glint
import Theorems.Thm_Formalism_UG_P_heckecomm_gelfand
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
variable {n : ℕ} {σ : L →+* L}
namespace GlobalTheory.UnitarySwap
theorem _root_.solution : HeckeCommU := by
  intro L _ _ _ ϖ σ q n k _ hU f₁ hf₁ f₂ hf₂
  have hint : ∀ i j, antiJ L n i j ∈ intL L := by
    intro i j; unfold antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨J, hJ, hJe⟩ := P.cartan_exists_glint (intL L) _ _ (antiJ_mul_self (L := L) (n := n)) hint hint
  refine P.heckecomm_gelfand (KU σ n) (fun g => g⁻¹) (fun x y => mul_inv_rev x y) (fun x => inv_inv x)
    (fun x hx => inv_mem hx) (fun g => ?_) f₁ f₂ hf₁.1 hf₂.1
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := inv_mem_doubleCoset hU hJ (g := (g : GL (Fin n) L)) (by
    intro i j
    rw [hJe]
    simp only [antiJ, add_comm i.val j.val]
    split_ifs <;> simp) (by rw [hJe]; exact g.2)
  rw [hJe] at hk₁ hk₂
  exact ⟨⟨⟨k₁, hk₁.1⟩, hk₁⟩, ⟨⟨k₂, hk₂.1⟩, hk₂⟩, Subtype.ext e⟩
end GlobalTheory.UnitarySwap
