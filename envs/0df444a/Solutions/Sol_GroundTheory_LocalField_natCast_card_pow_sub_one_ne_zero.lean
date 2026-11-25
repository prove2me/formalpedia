-- Prove2me | solution 1 for GroundTheory.LocalField.natCast_card_pow_sub_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:15.338656+00:00
-- url     : https://prove2.me/submissions/6d139325-545c-404e-8f68-cf1151611f97

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois

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
variable (K L)
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) :
    ((Nat.card 𝓀[K] ^ n - 1 : ℕ) : 𝓀[K]) ≠ 0 := by
  have := Fintype.ofFinite 𝓀[K]
  rw [Nat.cast_sub (Nat.one_le_pow _ _ Nat.card_pos), Nat.cast_pow, Nat.card_eq_fintype_card,
    FiniteField.cast_card_eq_zero, zero_pow hn, Nat.cast_one, zero_sub]
  exact neg_ne_zero.mpr one_ne_zero
end GroundTheory.LocalField
