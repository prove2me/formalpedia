-- Prove2me | solution 1 for GroundTheory.LocalField.residueDegree_eq_one_iff_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:03:55.913312+00:00
-- url     : https://prove2.me/submissions/6f1b5ec7-88ef-4f53-a609-0a0294ac40c2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_residueDegree_eq_finrank
import Theorems.Thm_GroundTheory_LocalField_residueDegree_eq_finrank


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
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F L] [ValuativeExtension F L]
    [FiniteDimensional F L] :
    residueDegree F L = 1 ↔ Function.Surjective (algebraMap 𝓀[F] 𝓀[L]) := by
  rw [residueDegree_eq_finrank, ← Subalgebra.bot_eq_top_iff_finrank_eq_one]
  constructor
  · intro h y
    have : y ∈ (⊥ : Subalgebra 𝓀[F] 𝓀[L]) := h ▸ Algebra.mem_top
    exact Algebra.mem_bot.1 this
  · intro h
    refine eq_top_iff.2 fun y _ ↦ Algebra.mem_bot.2 (h y)
end GroundTheory.LocalField
