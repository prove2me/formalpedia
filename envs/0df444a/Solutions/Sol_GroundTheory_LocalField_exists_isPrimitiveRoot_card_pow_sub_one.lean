-- Prove2me | solution 1 for GroundTheory.LocalField.exists_isPrimitiveRoot_card_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:54:25.818837+00:00
-- url     : https://prove2.me/submissions/36c24d6e-9950-4cc2-8b25-b7785adb7a05

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Theorems.Thm_GroundTheory_LocalField_natCast_card_pow_sub_one_ne_zero


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
open ValuativeRel IntermediateField
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ksep : Type*} [Field Ksep] [Algebra K Ksep]
namespace GroundTheory.LocalField
theorem _root_.solution [IsSepClosed Ksep] {n : ℕ} (hn : n ≠ 0) :
    ∃ ζ : Ksep, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1) := by
  have hK := natCast_ne_zero_of_residueField (natCast_card_pow_sub_one_ne_zero (K := K) hn)
  have : NeZero ((Nat.card 𝓀[K] ^ n - 1 : ℕ) : Ksep) := ⟨by
    rw [← map_natCast (algebraMap K Ksep)]
    exact (map_ne_zero_iff _ (algebraMap K Ksep).injective).mpr hK⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ksep _
end GroundTheory.LocalField
