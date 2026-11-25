-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.continuous_modCharacter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:43.211575+00:00
-- url     : https://prove2.me/submissions/89d8badf-4b79-4187-b2bf-2f8875d45ad2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
import Theorems.Thm_GroundTheory_Global_Cyclotomic_modCharacter_eq_one

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
theorem _root_.solution (n : ℕ) [NeZero n] :
    Continuous fun σ : Gal(ℚ̄/ℚ) => (modCharacter n σ : ZMod n) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ n
  have : FiniteDimensional ℚ ℚ⟮ζ⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  have hU := (ℚ⟮ζ⟯).fixingSubgroup_isOpen
  rw [continuous_discrete_rng]
  intro b
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨σ • ((ℚ⟮ζ⟯).fixingSubgroup : Set Gal(ℚ̄/ℚ)), ?_, hU.smul σ,
    ⟨1, one_mem _, mul_one σ⟩⟩
  rintro _ ⟨τ, hτ, rfl⟩
  have hτζ : τ ζ = ζ := (mem_fixingSubgroup_iff _ τ).mp hτ ζ (mem_adjoin_simple_self ℚ ζ)
  simp only [Set.mem_preimage, Set.mem_singleton_iff, smul_eq_mul, map_mul,
    modCharacter_eq_one hζ hτζ, mul_one] at hσ ⊢
  exact hσ
end GroundTheory.Global.Cyclotomic
