-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_infiniteCompletion_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:52:21.36588+00:00
-- url     : https://prove2.me/submissions/e0eaa5e2-c91b-48b9-9e50-8b114a9243bb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand
import Definitions.Def_GroundTheory_GlobalFields_InfiniteNormIndex_LocalSymbol
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrandInfinite
import Theorems.Thm_GroundTheory_Global_cycHerbrand_gal_completion_units
import Theorems.Thm_GroundTheory_Global_ofMulDistribMulAction_infiniteDecomposition_units
import Theorems.Thm_GroundTheory_Global_cycHerbrand_eq_of_mulEquiv
import Theorems.Thm_GroundTheory_Global_mem_zpowers_mulEquiv
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion GroundTheory.GroupCoh
open scoped NumberField.LiesOver
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K)
  (w : InfinitePlace L) [w.LiesOver v]
variable [IsGalois K L]
namespace GroundTheory.Global
theorem _root_.solution [Fintype (MulAction.stabilizer Gal(L/K) w)]
    (τ : MulAction.stabilizer Gal(L/K) w) (hτ : ∀ σ, σ ∈ Subgroup.zpowers τ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
          w.Completionˣ) τ)
        (cycNorm (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
          w.Completionˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
          w.Completionˣ) τ = Module.finrank v.Completion w.Completion := by
  obtain ⟨h1, h2⟩ := cycHerbrand_eq_of_mulEquiv
    (ρ' := Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w) w.Completionˣ)
    (ρ := Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion) w.Completionˣ)
    (infiniteDecompositionMulEquiv v w) (AddEquiv.refl _)
    (fun σ x ↦ ofMulDistribMulAction_infiniteDecomposition_units v w σ x) τ
  obtain ⟨h3, h4⟩ := cycHerbrand_gal_completion_units v w _
    (mem_zpowers_mulEquiv (infiniteDecompositionMulEquiv v w) hτ)
  exact ⟨h1.2 h3, h2.trans h4⟩
end GroundTheory.Global
