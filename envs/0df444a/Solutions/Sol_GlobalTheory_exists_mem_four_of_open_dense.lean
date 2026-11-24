-- Prove2me | solution 1 for GlobalTheory.exists_mem_four_of_open_dense
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:46.52703+00:00
-- url     : https://prove2.me/submissions/1a5c52ff-9a5f-4bfe-8a34-3650e3223492

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
omit [NormedSpace ℂ V]
namespace GlobalTheory
theorem _root_.solution {U : Set V} (ho : IsOpen U) (hd : Dense U)
    (e₁ e₂ e₃ e₄ : V ≃ₜ V) : ∃ x, e₁ x ∈ U ∧ e₂ x ∈ U ∧ e₃ x ∈ U ∧ e₄ x ∈ U := by
  have hD : ∀ e : V ≃ₜ V, Dense (e ⁻¹' U) := fun e => hd.preimage e.isOpenMap
  have hO : ∀ e : V ≃ₜ V, IsOpen (e ⁻¹' U) := fun e => ho.preimage e.continuous
  exact ((hD e₁).inter_of_isOpen_left ((hD e₂).inter_of_isOpen_left
    ((hD e₃).inter_of_isOpen_left (hD e₄) (hO e₃)) (hO e₂)) (hO e₁)).nonempty
end GlobalTheory
