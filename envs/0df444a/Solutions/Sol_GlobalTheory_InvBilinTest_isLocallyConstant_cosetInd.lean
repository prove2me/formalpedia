-- Prove2me | solution 1 for GlobalTheory.InvBilinTest.isLocallyConstant_cosetInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:52:14.318802+00:00
-- url     : https://prove2.me/submissions/383a91d7-ea02-455d-8ab4-51f09b81f4ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantCosetInd
import Theorems.Thm_GlobalTheory_InvBilinTest_cosetInd_apply
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
noncomputable section
open GlobalTheory GlobalTheory.InvBilinTest
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
namespace GlobalTheory.InvBilinTest
theorem _root_.solution (K : Subgroup G) (ho : IsOpen (K : Set G))
    (hK : IsCompact (K : Set G)) : IsLocallyConstant (cosetInd K ho hK) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨{h | g * h⁻¹ ∈ K}, ho.preimage (continuous_const.mul continuous_inv), by simp,
    fun h hh => Subtype.ext (funext fun x => ?_)⟩
  rw [cosetInd_apply, cosetInd_apply]
  have : x * h⁻¹ = x * g⁻¹ * (g * h⁻¹) := by group
  classical
  have hh' : g * h⁻¹ ∈ K := hh
  rw [this]
  exact if_congr (K.mul_mem_cancel_right hh') rfl rfl
end GlobalTheory.InvBilinTest
