-- Prove2me | solution 1 for GroundTheory.ProfCoh.kummerField_kummerGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:24:30.646632+00:00
-- url     : https://prove2.me/submissions/650a38ea-0c13-4d03-842b-9465c6422f5e

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerFinite
import Theorems.Thm_GroundTheory_ProfCoh_galEquivDual_apply
import Theorems.Thm_GroundTheory_ProfCoh_kummerGroupEquivDual_apply
import Theorems.Thm_GroundTheory_ProfCoh_kummerPairingLeft_apply
import Theorems.Thm_GroundTheory_ProfCoh_kummerPairingRight_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.kummerPairingLeft_apply
attribute [local simp] GroundTheory.ProfCoh.kummerPairingRight_apply


attribute [local simp] GroundTheory.ProfCoh.galEquivDual_apply
attribute [local simp] GroundTheory.ProfCoh.kummerGroupEquivDual_apply

set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open Polynomial
variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (L : Type*) [Field L] [Algebra K L]
variable {K n L}
variable (K n L)
namespace GroundTheory.ProfCoh
theorem _root_.solution [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    kummerField K n L (kummerGroup K n L) = ⊤ := by
  set E := kummerField K n L (kummerGroup K n L)
  have hbot : E.fixingSubgroup = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    apply kummerPairingLeft_injective K n L hexp
    rw [map_one]
    ext x : 1
    obtain ⟨a, ha, α, hα⟩ := exists_rep x
    have hαE : α ∈ E := IntermediateField.subset_adjoin _ _ ⟨a, ha ▸ x.2, hα⟩
    rw [kummerPairingLeft_apply, MonoidHom.one_apply]
    exact (kummerPairing_eq_one_iff σ x ha hα).mpr (hσ ⟨α, hαE⟩)
  rw [← IsGalois.fixedField_fixingSubgroup E, hbot, IntermediateField.fixedField_bot]
end GroundTheory.ProfCoh
