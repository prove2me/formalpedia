-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittSplit.exists_left_inv_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:12:29.984487+00:00
-- url     : https://prove2.me/submissions/0486fda6-bb1c-4b85-b6b1-a95f3856aa19

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale
import Theorems.Thm_GlobalTheory_SgAlg_WittSplit_exists_common_compl
import Theorems.Thm_GlobalTheory_SgAlg_WittSplit_inj_of_left
import Theorems.Thm_GlobalTheory_SgAlg_WittSplit_mat_eq_of_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittSplit
variable {F : Type} [Field F] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
namespace GlobalTheory.SgAlg.WittSplit
theorem _root_.solution (u u' : Matrix m k F) (hu : ∃ L : Matrix k m F, L * u = 1)
    (hu' : ∃ L : Matrix k m F, L * u' = 1) : ∃ L : Matrix k m F, L * u = 1 ∧ IsUnit (L * u').det := by
  have i := inj_of_left u hu
  have i' := inj_of_left u' hu'
  have hf : finrank F (LinearMap.range (Matrix.toLin' u)) = finrank F (LinearMap.range (Matrix.toLin' u')) := by
    rw [LinearMap.finrank_range_of_inj i, LinearMap.finrank_range_of_inj i']
  obtain ⟨S, hS, hS'⟩ := exists_common_compl _ _ _ rfl hf
  let e := LinearEquiv.ofInjective (Matrix.toLin' u) i
  let L0 : (m → F) →ₗ[F] (k → F) := e.symm.toLinearMap ∘ₗ Submodule.projectionOnto _ _ hS
  have hL0 : ∀ c, L0 (u *ᵥ c) = c := by
    intro c
    have hm : u *ᵥ c ∈ LinearMap.range (Matrix.toLin' u) := ⟨c, rfl⟩
    simp only [L0, LinearMap.comp_apply]
    rw [Submodule.projectionOnto_apply_left hS ⟨_, hm⟩]
    exact e.symm_apply_eq.2 (Subtype.ext (by simp [e]))
  refine ⟨LinearMap.toMatrix' L0, ?_, ?_⟩
  · exact mat_eq_of_mulVec _ _ fun c => by
      rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, hL0, Matrix.one_mulVec]
  · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    simp only [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec] at hxy
    have h0 : L0 (u' *ᵥ (x - y)) = 0 := by rw [Matrix.mulVec_sub, map_sub, hxy, sub_self]
    simp only [L0, LinearMap.comp_apply, LinearEquiv.coe_coe, map_eq_zero_iff _ e.symm.injective] at h0
    have hS0 := (Submodule.projectionOnto_apply_eq_zero_iff hS).1 h0
    have hU0 : u' *ᵥ (x - y) ∈ LinearMap.range (Matrix.toLin' u') := ⟨x - y, rfl⟩
    have hz : u' *ᵥ (x - y) = 0 := (Submodule.disjoint_def.1 hS'.disjoint) _ hU0 hS0
    have : x - y = 0 := i' (by simpa [Matrix.toLin'_apply] using hz)
    exact sub_eq_zero.1 this
end GlobalTheory.SgAlg.WittSplit
