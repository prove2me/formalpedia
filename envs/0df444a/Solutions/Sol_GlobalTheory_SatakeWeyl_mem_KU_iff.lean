-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.mem_KU_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:19:11.013747+00:00
-- url     : https://prove2.me/submissions/bc6158b9-d66a-4879-8c13-dd928851bd3e

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_mul_inv
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_inv_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_cartan_exists_glint
import Theorems.Thm_Formalism_UG_P_fSatake_K_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG
open GlobalTheory GlobalTheory.SatakeWeyl
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ n) :
    g ∈ KU σ n ↔ ∀ i j, mat g i j ∈ intL L := by
  refine ⟨fun h => P.fSatake_K_int h, fun h => ?_⟩
  have h' : ∀ i j, mat g⁻¹ i j ∈ intL L := fun i j => by
    rw [mat_inv_apply]
    show Valued.v (σ _) ≤ 1
    rw [hσ]
    exact h _ _
  obtain ⟨x, hx, e⟩ := P.cartan_exists_glint (intL L) _ _ (mat_mul_inv g) h h'
  have : x = (g : GL (Fin n) L) := Units.ext e
  rw [this] at hx
  exact ⟨g.2, hx⟩
end GlobalTheory.SatakeWeyl
