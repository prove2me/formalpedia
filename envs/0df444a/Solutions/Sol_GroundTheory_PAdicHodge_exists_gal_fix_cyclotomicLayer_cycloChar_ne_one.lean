-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_gal_fix_cyclotomicLayer_cycloChar_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:21:30.835653+00:00
-- url     : https://prove2.me/submissions/6c6669d1-26d5-485d-8f6b-6a4a3b44fd09

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_ExistsGalFixCyclotomicLayerCycloCharNeOne
import Theorems.Thm_GroundTheory_PAdicHodge_cycloChar_spec
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_cycl
import Theorems.Thm_GroundTheory_PAdicHodge_le_cyclotomicLayer
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_GroundTheory_PAdicHodge_totient_prime_pow_succ
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField UniformSpace
variable {p : ℕ} [hp : Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] K]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (n : ℕ) :
    ∃ σ : Gal(PadicAlgCl p/K), (∀ y ∈ cyclotomicLayer K n, σ y = y) ∧ cycloChar K σ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  set E : IntermediateField K (PadicAlgCl p) := extendScalars (le_cyclotomicLayer K n)
  have hcyc : ∀ m, cycl p m ≤ cyclotomicLayer K n := by
    intro m
    refine adjoin_le_iff.2 fun ζ hζ => ?_
    have hζ' : ζ ^ p ^ m = 1 := hζ
    have hmem : ζ ∈ fixedField E.fixingSubgroup := by
      rw [mem_fixedField_iff]
      intro σ hσ
      have hσ' : ∀ y ∈ cyclotomicLayer K n, σ y = y := fun y hy =>
        (mem_fixingSubgroup_iff _ _).1 hσ y hy
      have h1 := hcon σ hσ'
      rw [cycloChar_spec K σ hζ', h1, Units.val_one, map_one]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp only [pow_zero, pow_one] at hζ'
        simp [hζ']
      · have hp1 : p ^ m ≠ 1 := (Nat.one_lt_pow hm.ne' hp.out.one_lt).ne'
        rw [ZMod.val_one'' hp1, pow_one]
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
    exact hmem
  have hle := IntermediateField.finrank_le_of_le_right (hcyc (Module.finrank ℚ_[p] (cyclotomicLayer K n) + 1))
  rw [finrank_cycl, Nat.totient_prime_pow_succ hp.out] at hle
  have h1 : Module.finrank ℚ_[p] (cyclotomicLayer K n) < p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) :=
    Nat.lt_pow_self hp.out.one_lt
  have h2 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
  have h3 : p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) ≤
      p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) * (p - 1) := Nat.le_mul_of_pos_right _ h2
  omega
end GroundTheory.PAdicHodge
