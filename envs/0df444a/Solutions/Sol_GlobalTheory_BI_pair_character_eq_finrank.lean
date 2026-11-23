-- Prove2me | solution 1 for GlobalTheory.BI.pair_character_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:47.512039+00:00
-- url     : https://prove2.me/submissions/8e72dd10-a395-4298-a9dc-349f1671614f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingCharacterEqFinrankInte

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
namespace _root_.GlobalTheory.BI
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W), _root_.GlobalTheory.BI.pair (fun g => algebraMap K L (σ.character g)) (fun g => algebraMap K L (ρ.character g)) = (Module.finrank K (Representation.IntertwiningMap ρ σ) : L) := by
  intro K L _ _ _ _ _ G _ _ V _ _ _ W _ _ _ ρ σ
  classical
  haveI := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have h := congrArg (algebraMap K L)
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ)
  unfold _root_.GlobalTheory.BI.pair
  rw [finsum_eq_sum_of_fintype]
  simpa only [map_mul, map_sum, map_inv₀, map_natCast] using h
end _root_.GlobalTheory.BI
end GlobalTheory.BI
