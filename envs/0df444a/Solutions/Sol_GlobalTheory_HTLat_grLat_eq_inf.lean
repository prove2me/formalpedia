-- Prove2me | solution 1 for GlobalTheory.HTLat.grLat_eq_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:51:50.087517+00:00
-- url     : https://prove2.me/submissions/c0d50580-a661-4269-ab35-d20d10272c03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Theorems.Thm_GlobalTheory_HTLat_grLat_le
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U]
namespace GlobalTheory.HTLat
theorem _root_.solution (La : Submodule O U) {F' F : Submodule C U} (h : F' ≤ F) :
    grLat La F' F = La.map (F'.mkQ.restrictScalars O) ⊓ (F.map F'.mkQ).restrictScalars O := by
  refine le_antisymm (le_inf (Submodule.map_mono inf_le_left) (grLat_le La F' F)) ?_
  rintro _ ⟨⟨x, hx, rfl⟩, y, hy, hxy⟩
  refine ⟨x, ⟨hx, ?_⟩, rfl⟩
  have h1 : y - x ∈ F' := (Submodule.Quotient.eq F').1 hxy
  have h2 := F.sub_mem hy (h h1)
  simpa using h2
end GlobalTheory.HTLat
