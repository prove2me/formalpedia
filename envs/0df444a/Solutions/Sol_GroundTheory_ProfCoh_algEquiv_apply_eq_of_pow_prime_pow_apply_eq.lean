-- Prove2me | solution 1 for GroundTheory.ProfCoh.algEquiv_apply_eq_of_pow_prime_pow_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:07.869186+00:00
-- url     : https://prove2.me/submissions/902a2c88-2b32-4d17-993a-5c69463ce743

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
import Theorems.Thm_GroundTheory_LocalField_ramificationQuotientToUnits_mk
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.ramificationQuotientToUnits_mk
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.LocalField ValuativeRel IntermediateField
namespace GroundTheory.ProfCoh
theorem _root_.solution {K L : Type*} [Field K] [Field L]
    [Algebra K L] {l : ℕ} (hl : l.Prime) {ζ : L} (hζ : ζ ^ l = 1) (σ : L ≃ₐ[K] L) {n : ℕ}
    (h : (σ ^ l ^ n) ζ = ζ) : σ ζ = ζ := by
  rcases (Nat.dvd_prime hl).1 (orderOf_dvd_of_pow_eq_one hζ) with h1 | hl'
  · rw [orderOf_eq_one_iff.1 h1, map_one]
  have hprim : IsPrimitiveRoot ζ l := hl' ▸ IsPrimitiveRoot.orderOf ζ
  have : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one (ξ := σ ζ) (by rw [← map_pow, hζ, map_one])
  have key : ∀ m : ℕ, (σ ^ m) ζ = ζ ^ k ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, AlgEquiv.mul_apply, ← hk, map_pow, ih, ← pow_mul, ← pow_succ]
  have hmod : ∀ a : ℕ, ζ ^ a = ζ ^ (a % l) := fun a ↦ by
    conv_lhs => rw [← Nat.div_add_mod a l, pow_add, pow_mul, hζ, one_pow, one_mul]
  have hkm : k ^ l ^ n % l = k % l := by
    have := Fact.mk hl
    rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_pow, ZMod.pow_card_pow]
  rw [key] at h
  calc σ ζ = ζ ^ k := hk.symm
    _ = ζ ^ (k ^ l ^ n % l) := by rw [hkm, ← hmod]
    _ = ζ := by rw [← hmod, h]
end GroundTheory.ProfCoh
