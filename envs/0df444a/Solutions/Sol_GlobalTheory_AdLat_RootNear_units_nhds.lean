-- Prove2me | solution 1 for GlobalTheory.AdLat.RootNear.units_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:54:10.027857+00:00
-- url     : https://prove2.me/submissions/6f702429-52a8-40d7-9801-38cb344793c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdeleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsRootNear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.RootNear
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.AdLat.RootNear
theorem _root_.solution {M : Type} [Monoid M] [TopologicalSpace M] (W : Set Mˣ) (hW : W ∈ 𝓝 (1 : Mˣ)) :
    ∃ V ∈ 𝓝 (1 : M), ∀ x : Mˣ, (x : M) ∈ V → ((x⁻¹ : Mˣ) : M) ∈ V → x ∈ W := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨T, hT, hTW⟩ := hW
  rw [map_one] at hT
  obtain ⟨V₁, h₁, V₂, h₂, hsub⟩ := mem_nhds_prod_iff.1 hT
  have h₃ : MulOpposite.op ⁻¹' V₂ ∈ 𝓝 (1 : M) := MulOpposite.continuous_op.continuousAt.preimage_mem_nhds h₂
  exact ⟨_, Filter.inter_mem h₁ h₃, fun x hx hy => hTW (hsub ⟨hx.1, hy.2⟩)⟩
end GlobalTheory.AdLat.RootNear
