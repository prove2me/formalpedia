-- Prove2me | solution 1 for GlobalTheory.isInvariant_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:03:34.391533+00:00
-- url     : https://prove2.me/submissions/f9bd8b74-a1a6-41ee-9137-3509860c8b47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_isInvariant_of_isBaseChange
import Theorems.Thm_GlobalTheory_faithfulSMul_of_isBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable (G : Type*) [Group G]
variable {A : Type*} [CommRing A] [MulSemiringAction G A]
variable {B : Type*} [CommRing B] [Algebra B A] [SMulCommClass G B A]
namespace GlobalTheory
theorem _root_.solution [Finite G] [Algebra.IsInvariant B A G]
    (T : Submonoid B) (B' A' : Type*) [CommRing B'] [CommRing A'] [Algebra B B'] [Algebra A A']
    [Algebra B' A'] [Algebra B A'] [IsScalarTower B B' A'] [IsScalarTower B A A']
    [IsLocalization T B'] [IsLocalization (Algebra.algebraMapSubmonoid A T) A']
    [MulSemiringAction G A'] [SMulDistribClass G A A'] :
    SMulCommClass G B' A' ∧ Algebra.IsInvariant B' A' G ∧
      (FaithfulSMul B A → FaithfulSMul B' A') := by
  haveI := IsLocalization.flat B' T
  have hf : ∀ (g : G) a, algebraMap A A' (g • a) = g • algebraMap A A' a := fun g a ↦ by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_distrib_smul, smul_one]
  have hfix : ∀ (g : G) (b : B'), g • algebraMap B' A' b = algebraMap B' A' b := fun g b ↦ by
    change ((MulSemiringAction.toRingHom G A' g).comp (algebraMap B' A')) b = _
    congr 1
    refine IsLocalization.ringHom_ext T ?_
    ext b
    simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B A A', ← hf,
      smul_algebraMap]
  haveI : SMulCommClass G B' A' :=
    ⟨fun g b x ↦ by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have hb : IsBaseChange B' (IsScalarTower.toAlgHom B A A').toLinearMap :=
    (isLocalizedModule_iff_isBaseChange T B' _).mp
      (isLocalizedModule_iff_isLocalization.mpr inferInstance)
  exact ⟨this, isInvariant_of_isBaseChange G _ hb hf, fun _ ↦ faithfulSMul_of_isBaseChange _ hb⟩
end GlobalTheory
