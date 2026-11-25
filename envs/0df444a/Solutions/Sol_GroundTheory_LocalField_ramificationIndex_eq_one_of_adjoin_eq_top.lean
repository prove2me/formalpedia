-- Prove2me | solution 1 for GroundTheory.LocalField.ramificationIndex_eq_one_of_adjoin_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:44:06.766577+00:00
-- url     : https://prove2.me/submissions/864da7c1-3851-4214-a414-9d1ffbd42af3

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_mul_residueDegree
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_pos
import Theorems.Thm_GroundTheory_LocalField_residueDegree_eq_finrank
import Theorems.Thm_GroundTheory_LocalField_residueDegree_pos


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
open ValuativeRel Polynomial IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {m : ℕ} {ζ : L}
namespace GroundTheory.LocalField
theorem _root_.solution (hζ : IsPrimitiveRoot ζ m) (hm : (m : 𝓀[K]) ≠ 0)
    (htop : K⟮ζ⟯ = ⊤) : ramificationIndex K L = 1 := by
  have := isGalois_of_adjoin_eq_top hζ (natCast_ne_zero_of_residueField (L := K) hm) htop
  have hinj := residueAlgEquiv_injective_of_adjoin_eq_top K L hm hζ.pow_eq_one htop
  have hcard : Module.finrank K L ≤ residueDegree K L := by
    rw [← IsGalois.card_aut_eq_finrank, residueDegree_eq_finrank, ← IsGalois.card_aut_eq_finrank]
    exact Nat.card_le_card_of_injective _ hinj
  have hf := residueDegree_pos K L
  rw [← ramificationIndex_mul_residueDegree K L] at hcard
  have he := ramificationIndex_pos K L
  nlinarith
end GroundTheory.LocalField
