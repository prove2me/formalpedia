-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_gal_completion_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:55:30.62631+00:00
-- url     : https://prove2.me/submissions/0ad0432f-8c14-47a6-a9de-0321082a4ae5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand
import Definitions.Def_GroundTheory_GlobalFields_InfiniteNormIndex_LocalSymbol
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrandInfinite
import Theorems.Thm_GroundTheory_Global_hasHerbrandQuotient_of_cycHerbrand_ne_zero
import Theorems.Thm_GroundTheory_Global_ofMulDistribMulAction_gal_completion_units
import Theorems.Thm_GroundTheory_Global_InfinitePlace_cyclicHerbrand_unitsRep_eq_finrank
import Theorems.Thm_GroundTheory_Global_cycHerbrand_eq_of_mulEquiv
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
namespace GroundTheory.Global
theorem _root_.solution (σ : Gal(w.Completion/v.Completion))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion)
          w.Completionˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion)
          w.Completionˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion)
          w.Completionˣ) σ = Module.finrank v.Completion w.Completion := by
  have h1 := (cycHerbrand_eq_of_mulEquiv
    (ρ' := Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion) w.Completionˣ)
    (ρ := InfinitePlace.unitsRep v w) (MulEquiv.refl _) (AddEquiv.refl _)
    (fun g x ↦ ofMulDistribMulAction_gal_completion_units v w g x) σ).2
  have h2 : cycHerbrand (InfinitePlace.unitsRep v w) σ = Module.finrank v.Completion w.Completion :=
    InfinitePlace.cyclicHerbrand_unitsRep_eq_finrank v w σ hσ
  have h3 : cycHerbrand (Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion)
      w.Completionˣ) σ = Module.finrank v.Completion w.Completion := h1.trans h2
  refine ⟨hasHerbrandQuotient_of_cycHerbrand_ne_zero ?_, h3⟩
  rw [h3, Nat.cast_ne_zero]
  exact Module.finrank_pos.ne'
end GroundTheory.Global
