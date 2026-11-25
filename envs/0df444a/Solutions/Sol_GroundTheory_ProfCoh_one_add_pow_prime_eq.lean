-- Prove2me | solution 1 for GroundTheory.ProfCoh.one_add_pow_prime_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:25:44.345013+00:00
-- url     : https://prove2.me/submissions/5e0d7b8a-0fdd-48e7-9071-51dfc5855155

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsPower
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.ProfCoh
theorem _root_.solution {p : ℕ} (hp : p.Prime) {z : 𝒪[K]} (hz : z ∈ 𝓂[K]) :
    ∃ y ∈ 𝓂[K], (1 + z) ^ p = 1 + z ^ p + p * z * (1 + y) := by
  rw [add_comm (1 : 𝒪[K]) z, add_pow_prime_eq hp z 1]
  set r := ∑ k ∈ Finset.Ioo 0 p, z ^ (k - 1) * 1 ^ (p - k - 1) * ((p.choose k / p : ℕ) : 𝒪[K])
  refine ⟨r - 1, ?_, by ring⟩
  rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
  have hz' : residue 𝒪[K] z = 0 := (residue_eq_zero_iff _).mpr hz
  simp only [r, map_sum, map_mul, map_pow, hz', one_pow, map_natCast, mul_one]
  rw [Finset.sum_eq_single 1]
  · simp [Nat.div_self hp.pos]
  · intro k hk hk1
    have : k - 1 ≠ 0 := by simp at hk; omega
    simp [zero_pow this]
  · intro h
    exact absurd (by simp; exact hp.one_lt) h
end GroundTheory.ProfCoh
