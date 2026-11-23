-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.exists_modCharacter_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:00.993677+00:00
-- url     : https://prove2.me/submissions/42018e1e-ffaf-4998-991a-79a68477248c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
import Theorems.Thm_GroundTheory_Global_Cyclotomic_modCharacter_eq_of_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
open scoped Pointwise
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
variable {n : ℕ} [NeZero n]
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    ∃ σ : Gal(ℚ̄/ℚ), modCharacter n σ = a := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ n
  have : IsCyclotomicExtension {n} ℚ ℚ⟮ζ⟯ := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : NumberField ℚ⟮ζ⟯ := IsCyclotomicExtension.numberField {n} ℚ _
  let τ := (IsCyclotomicExtension.Rat.galEquivZMod n ℚ⟮ζ⟯).symm a
  let ζ' : ℚ⟮ζ⟯ := ⟨ζ, mem_adjoin_simple_self ℚ ζ⟩
  have hζ' : ζ' ^ n = 1 := Subtype.ext hζ.pow_eq_one
  have hτ := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n ℚ⟮ζ⟯ τ hζ'
  rw [MulEquiv.apply_symm_apply] at hτ
  refine ⟨τ.liftNormal ℚ̄, Units.ext (modCharacter_eq_of_apply hζ ?_)⟩
  have := AlgEquiv.liftNormal_commutes τ ℚ̄ ζ'
  rw [hτ, map_pow] at this
  exact this
end GroundTheory.Global.Cyclotomic
