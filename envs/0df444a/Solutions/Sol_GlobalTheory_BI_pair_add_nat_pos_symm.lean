-- Prove2me | solution 1 for GlobalTheory.BI.pair_add_nat_pos_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:24.804038+00:00
-- url     : https://prove2.me/submissions/e243df5a-e409-4d6e-aaf4-f4fc01843b88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingAddNatPosSymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.BI
namespace GlobalTheory.BI
private theorem character_pairing_eq_finrank_hom (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K]
    (G : Type) [Group G] [Finite G] {n m : ℕ} (ρ : Representation K G (Fin n → K))
    (σ : Representation K G (Fin m → K)) :
    pair (fun g => algebraMap K L (σ.character g)) (fun g => algebraMap K L (ρ.character g))
      = (Module.finrank K (Representation.IntertwiningMap ρ σ) : L) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hK := congrArg (algebraMap K L)
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ)
  rw [map_natCast] at hK
  rw [← hK]
  simp only [pair, finsum_eq_sum_of_fintype, map_mul, map_inv₀, map_natCast, map_sum]
end GlobalTheory.BI
end

set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G], (∀ a b c : G → L, pair (a + b) c = pair a c + pair b c) ∧ (∀ a b : G → L, IsChar K L a → IsChar K L b → ∃ n : ℕ, pair a b = (n : L)) ∧ (∀ φ : G → L, IsIrrChar K L φ → ∃ n : ℕ, 0 < n ∧ pair φ φ = (n : L)) ∧ ∀ a b : G → L, pair a b = pair b a := by
  intro K L _ _ _ _ _ G _ _
  classical
  have : Fintype G := Fintype.ofFinite G
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c
    simp only [pair, finsum_eq_sum_of_fintype, Pi.add_apply, add_mul, Finset.sum_add_distrib,
      mul_add]
  · rintro a b ⟨n, ρ, hρ⟩ ⟨m, σ, hσ⟩
    refine ⟨Module.finrank K (Representation.IntertwiningMap σ ρ), ?_⟩
    rw [show a = fun g => algebraMap K L (ρ.character g) from funext hρ,
      show b = fun g => algebraMap K L (σ.character g) from funext hσ]
    exact character_pairing_eq_finrank_hom K L G σ ρ
  · rintro φ ⟨n, ρ, hirr, hρ⟩
    refine ⟨Module.finrank K (Representation.IntertwiningMap ρ ρ), ?_, ?_⟩
    · have : IsSimpleModule (MonoidAlgebra K G) ρ.asModule :=
        (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
      have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra K G) _
      obtain ⟨v, hv⟩ : ∃ v : Fin n → K, v ≠ 0 := exists_ne (0 : ρ.asModule)
      have : Nontrivial (Representation.IntertwiningMap ρ ρ) :=
        ⟨⟨Representation.IntertwiningMap.id ρ, 0, fun h => hv (by
          have hv0 := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) h
          rwa [Representation.IntertwiningMap.id_apply, Representation.IntertwiningMap.coe_zero,
            Pi.zero_apply] at hv0)⟩⟩
      have : Module.Finite K (Representation.IntertwiningMap ρ ρ) :=
        Module.Finite.equiv (Representation.invariantsEquivIntertwiningMap ρ ρ)
      exact Module.finrank_pos
    · rw [show φ = fun g => algebraMap K L (ρ.character g) from funext hρ]
      exact character_pairing_eq_finrank_hom K L G ρ ρ
  · intro a b
    simp only [pair, finsum_eq_sum_of_fintype]
    congr 1
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => by simp [mul_comm])
end GlobalTheory.BI
