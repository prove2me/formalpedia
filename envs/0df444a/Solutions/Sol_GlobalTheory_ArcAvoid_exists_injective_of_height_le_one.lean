-- Prove2me | solution 1 for GlobalTheory.ArcAvoid.exists_injective_of_height_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:48.00592+00:00
-- url     : https://prove2.me/submissions/240c9e3d-1430-4c2b-9f1d-28e6c3aa438e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_StalkGenericPointSpecializesOfSpecializes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRingEquivPowerSeriesOfComplete
import Theorems.Thm_GlobalTheory_ArcAvoid_exists_ringHom_powerSeries_of_dvr
import Theorems.Thm_GlobalTheory_ArcAvoid_surjective_residue_of_isAlgebraic
import Theorems.Thm_GlobalTheory_exists_valuationSubring_of_height_le_one
import Theorems.Thm_GlobalTheory_krullAkizuki
import Theorems.Thm_GlobalTheory_powerSeriesPrimeX_asIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.powerSeriesPrimeX_asIdeal



set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.ArcAvoid
open Polynomial
namespace GlobalTheory.ArcAvoid
theorem _root_.solution {k B : Type*} [Field k] [IsAlgClosed k] [CommRing B]
    [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] (m : Ideal B) [hm : m.IsMaximal]
    (h1 : m.height ≤ 1) :
    ∃ φ : B →ₐ[k] PowerSeries k, Function.Injective φ ∧
      ∀ b, b ∈ m ↔ PowerSeries.constantCoeff (φ b) = 0 := by
  rcases eq_or_ne m ⊥ with rfl | hne
  · letI : Field B := (Ring.isField_iff_maximal_bot.mpr hm).toField
    have : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
    let e : k ≃ₐ[k] B :=
      .ofBijective (Algebra.ofId k B) IsAlgClosed.algebraMap_bijective_of_isIntegral
    refine ⟨(Algebra.ofId k (PowerSeries k)).comp e.symm, RingHom.injective _, fun b => ?_⟩
    simp [Algebra.ofId_apply]
  obtain ⟨t, htm, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  letI : Algebra k[X] B := (aeval t : k[X] →ₐ[k] B).toRingHom.toAlgebra
  have hal : ∀ p : k[X], algebraMap k[X] B p = aeval t p := fun _ => rfl
  have : IsScalarTower k k[X] B := .of_algebraMap_eq fun a => by simp [hal]
  have : Algebra.FiniteType k[X] B := .of_restrictScalars_finiteType k k[X] B
  have hinj : Function.Injective (algebraMap k[X] B) := by
    refine transcendental_iff_injective.mp fun halg => hm.ne_top ?_
    exact m.eq_top_of_isUnit_mem htm (halg.isIntegral.isUnit ht0)
  obtain ⟨K', _, _, _, V, φ, hφ, hφi, hφm⟩ := exists_valuationSubring_of_height_le_one
    (O := k[X]) (K := FractionRing k[X]) hinj m h1 X X_ne_zero (by simpa [hal] using htm)
  letI : Algebra k[X] V := (φ.comp (algebraMap k[X] B)).toAlgebra
  letI : Algebra k[X] K' :=
    ((algebraMap (FractionRing k[X]) K').comp (algebraMap k[X] (FractionRing k[X]))).toAlgebra
  have : IsScalarTower k[X] (FractionRing k[X]) K' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k[X] V K' := .of_algebraMap_eq fun a => (hφ a).symm
  have : FaithfulSMul k[X] V := (faithfulSMul_iff_algebraMap_injective _ _).mpr (hφi.comp hinj)
  have halg : Algebra.IsAlgebraic k[X] K' :=
    (IsFractionRing.comap_isAlgebraic_iff (A := k[X]) (K := FractionRing k[X]) (C := K')).mpr
      inferInstance
  have : Algebra.IsAlgebraic k[X] V :=
    .of_injective (IsScalarTower.toAlgHom k[X] V K') Subtype.val_injective
  have hXV : algebraMap k[X] V X ∈ maximalIdeal V := by
    change algebraMap k[X] B X ∈ (maximalIdeal V).comap φ
    simpa [hal, hφm] using htm
  let W : Subalgebra k[X] K' :=
    { V.toSubring with algebraMap_mem' := fun r => (hφ r) ▸ (φ (algebraMap k[X] B r)).2 }
  have hVn : IsNoetherianRing V := (krullAkizuki (FractionRing k[X]) W).1
  have hnf : ¬ IsField V := by
    rw [isField_iff_maximalIdeal_eq]
    intro h
    rw [h] at hXV
    exact X_ne_zero ((FaithfulSMul.algebraMap_eq_zero_iff k[X] V).mp hXV)
  have hval : ValuationRing V := inferInstance
  have : IsDiscreteValuationRing V := ((IsDiscreteValuationRing.TFAE V hnf).out 1 0).mp hval
  obtain ⟨ψ, hψi, hψC, hψm⟩ :=
    exists_ringHom_powerSeries_of_dvr _ (surjective_residue_of_isAlgebraic hXV)
  refine ⟨{ ψ.comp φ with commutes' := fun a => ?_ }, hψi.comp hφi, fun b => ?_⟩
  · have := hψC a
    rw [IsScalarTower.algebraMap_apply k k[X] B]
    exact this
  · rw [← hφm]
    exact hψm (φ b)
end GlobalTheory.ArcAvoid
