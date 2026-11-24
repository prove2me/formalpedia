-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.TestNearE.exists_nhds_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:34:59.405482+00:00
-- url     : https://prove2.me/submissions/d4b7b887-40e6-49b3-89ff-825747b8b1c1

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentity
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open GlobalTheory GlobalTheory.GodementJacquet GlobalTheory.GodementJacquet.TestNearE
open ValuativeRel Filter Topology
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.GodementJacquet.TestNearE
theorem _root_.solution (r : ℕ) (S : Set (GL (Fin r) k)) (hS : IsOpen S) (h1 : (1 : GL (Fin r) k) ∈ S) :
    ∃ W ∈ 𝓝 (1 : Matrix (Fin r) (Fin r) k), ∀ g : GL (Fin r) k, g.val ∈ W → g ∈ S := by
  obtain ⟨U, hU, hUS⟩ := (Units.isEmbedding_embedProduct (M := Matrix (Fin r) (Fin r) k)).isInducing.isOpen_iff.mp hS
  let φ : Matrix (Fin r) (Fin r) k → Matrix (Fin r) (Fin r) k × (Matrix (Fin r) (Fin r) k)ᵐᵒᵖ :=
    fun x => (x, MulOpposite.op x⁻¹)
  have hφ : ContinuousAt φ 1 := by
    refine continuousAt_id.prodMk (MulOpposite.continuous_op.continuousAt.comp ?_)
    apply continuousAt_matrix_inv
    rw [Matrix.det_one, Ring.inverse_eq_inv']
    exact continuousAt_inv₀ one_ne_zero
  have hemb : ∀ g : GL (Fin r) k, Units.embedProduct _ g = φ g.val := by
    intro g
    simp [φ, Units.embedProduct_apply, Matrix.coe_units_inv]
  refine ⟨φ ⁻¹' U, hφ.preimage_mem_nhds (hU.mem_nhds ?_), fun g hg => ?_⟩
  · have : (1 : GL (Fin r) k) ∈ Units.embedProduct _ ⁻¹' U := by rw [hUS]; exact h1
    simpa [hemb] using this
  · rw [← hUS]
    show Units.embedProduct _ g ∈ U
    rw [hemb]; exact hg
end GlobalTheory.GodementJacquet.TestNearE
