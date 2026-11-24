-- Prove2me | solution 1 for GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:02:41.990363+00:00
-- url     : https://prove2.me/submissions/5d2a2000-17b0-48c3-8371-2424e24f5b31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLinearOfBilinearSchwartzBruhatProduct
import Theorems.Thm_GlobalTheory_LocFlat_CFac_tensorToProd_tmul
import Theorems.Thm_GlobalTheory_LocFlat_CFac_tensorToProd_injective
import Theorems.Thm_GlobalTheory_LocFlat_CFac_mulLC_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LocFlat.CFac.mulLC_apply



set_option autoImplicit false
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.CFac
namespace GlobalTheory.LocFlat.CFac
theorem _root_.solution : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (M : Type) [AddCommGroup M] [Module ℂ M] (B : SB X →ₗ[ℂ] SB Y →ₗ[ℂ] M), ∃ l : SB (X × Y) →ₗ[ℂ] M, ∀ f g, l (prodSB f g) = B f g := by
  intro X Y _ _ M _ _ B
  let m := tensorToProd X Y
  let e := LinearEquiv.ofInjective m (tensorToProd_injective X Y)
  let l₀ : LinearMap.range m →ₗ[ℂ] M := (TensorProduct.lift B).comp e.symm.toLinearMap
  obtain ⟨l, hl⟩ := LinearMap.exists_extend l₀
  refine ⟨l, fun f g => ?_⟩
  have hmem : prodSB f g = ((e (f ⊗ₜ g) : LinearMap.range m) : SB (X × Y)) := by
    simp [e, LinearEquiv.ofInjective_apply, m, tensorToProd_tmul]
  have := LinearMap.congr_fun hl (e (f ⊗ₜ g))
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, l₀,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, TensorProduct.lift.tmul] at this
  rw [hmem, this]
end GlobalTheory.LocFlat.CFac
