-- Prove2me | solution 1 for GroundTheory.Automorphic.mem_range_normUnits_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:50:25.575031+00:00
-- url     : https://prove2.me/submissions/735e0c94-fdd5-4e84-bf45-0a48568d4ce3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWittExtension
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSplit
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianClassification
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_normUnits



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
namespace GroundTheory.Automorphic
theorem _root_.solution (u : Fˣ) :
    u ∈ (normUnits F E).range ↔ ∃ z : E, Algebra.norm F z = u := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, (coe_normUnits w).symm⟩
  · rintro ⟨z, hz⟩
    have hz0 : z ≠ 0 := by rintro rfl; rw [Algebra.norm_zero] at hz; exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by rw [coe_normUnits, Units.val_mk0, hz])⟩
end GroundTheory.Automorphic
