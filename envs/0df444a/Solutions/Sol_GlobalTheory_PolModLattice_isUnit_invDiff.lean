-- Prove2me | solution 1 for GlobalTheory.PolModLattice.isUnit_invDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:27:11.468746+00:00
-- url     : https://prove2.me/submissions/286a9e99-c34e-4e96-905d-87ea88c16e2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
open GlobalTheory GlobalTheory.PolModLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open scoped nonZeroDivisors
namespace GlobalTheory.PolModLattice
theorem _root_.solution : IsUnit (invDiff E) := by
  let K := maximalRealSubfield E
  let f : K →ₐ[OF E] E := IsScalarTower.toAlgHom (OF E) K E
  haveI : NeZero (1 : FractionalIdeal (OF E)⁰ K) := ⟨one_ne_zero⟩
  let 𝔡 : FractionalIdeal (OF E)⁰ K := FractionalIdeal.dual ℤ ℚ 1
  have h0 : 𝔡 ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have hmul : (𝔡 : Submodule (OF E) K) * ((𝔡⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K) = 1 := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ h0, FractionalIdeal.coe_one]
  have heq : invDiff E = (𝔡 : Submodule (OF E) K).map f.toLinearMap := by
    ext v
    constructor
    · rintro ⟨w, rfl, hw⟩
      refine ⟨w, ?_, rfl⟩
      show w ∈ 𝔡
      rw [FractionalIdeal.mem_dual one_ne_zero]
      intro a ha
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      obtain ⟨n, hn⟩ := hw b
      exact ⟨n, by rw [Algebra.traceForm_apply]; simpa using hn.symm⟩
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w, rfl, fun a => ?_⟩
      have hw' : w ∈ 𝔡 := hw
      rw [FractionalIdeal.mem_dual one_ne_zero] at hw'
      obtain ⟨n, hn⟩ := hw' (algebraMap (OF E) K a) ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
      exact ⟨n, by rw [Algebra.traceForm_apply] at hn; simpa using hn.symm⟩
  refine ⟨⟨invDiff E, ((𝔡⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K).map f.toLinearMap, ?_, ?_⟩, rfl⟩
  · rw [heq, ← Submodule.map_mul, hmul, Submodule.map_one]
  · rw [heq, ← Submodule.map_mul, mul_comm, hmul, Submodule.map_one]
end GlobalTheory.PolModLattice
