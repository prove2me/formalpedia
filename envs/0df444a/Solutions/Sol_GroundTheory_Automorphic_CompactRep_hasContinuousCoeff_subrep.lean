-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactRep.hasContinuousCoeff_subrep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:28:38.781089+00:00
-- url     : https://prove2.me/submissions/fdcb279c-dc05-4204-9e55-bf5c0dd6cb05

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CompactRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_5d0ada4687d5
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_5d0ada4687d5
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.CompactRep
open Module Set
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {X : Type*} [AddCommGroup X] [Module ℂ X]
variable {σ : Representation ℂ K X}
namespace GroundTheory.Automorphic.CompactRep
theorem _root_.solution (hσ : Representation.HasContinuousCoeff σ)
    (P : Subrepresentation σ) : Representation.HasContinuousCoeff P.toRepresentation := by
  intro φ w
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ
  have : ∀ k, φ (P.toRepresentation k w) = ψ (σ k w) := fun k => by
    rw [← hψ]
    rfl
  simp only [this]
  exact hσ ψ w
end GroundTheory.Automorphic.CompactRep
