-- Prove2me | solution 1 for GlobalTheory.FibreFlatGen.flat_of_injective_on_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:13:52.665885+00:00
-- url     : https://prove2.me/submissions/6cd15f95-6aac-4629-94f8-37a78ef999dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatOfIsFiniteOfFlatGeometricFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RTensorInjectiveOfFlatBaseChange
import Theorems.Thm_GlobalTheory_FibreFlatGen_relationsLift_succ
import Theorems.Thm_GlobalTheory_LocalFlat_flat_of_relationsLift
import Theorems.Thm_GlobalTheory_LocalFlat_range_lTensor_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory GlobalTheory.FibreFlatGen
open LocalFlat
universe u
namespace GlobalTheory.FibreFlatGen
theorem _root_.solution {R : Type*} {A : Type u} {L : Type*} [CommRing R] [CommRing A]
    [CommRing L] [Algebra R A] [Algebra A L] [Algebra R L] [IsScalarTower R A L]
    [IsNoetherianRing A] [IsNoetherianRing L] [Module.Flat R L] (J : Ideal R)
    (hJ : (J.map (algebraMap R A)).map (algebraMap A L) ≤ Ideal.jacobson ⊥)
    (hinj : ∀ (N' N : Type u) [AddCommGroup N'] [AddCommGroup N]
      [Module (A ⧸ J.map (algebraMap R A)) N'] [Module (A ⧸ J.map (algebraMap R A)) N]
      [Module A N'] [Module A N] [IsScalarTower A (A ⧸ J.map (algebraMap R A)) N']
      [IsScalarTower A (A ⧸ J.map (algebraMap R A)) N]
      (ι : N' →ₗ[A ⧸ J.map (algebraMap R A)] N), Function.Injective ι →
        Function.Injective ((ι.restrictScalars A).lTensor L)) :
    Module.Flat A L := by
  refine flat_of_relationsLift L hJ fun n => ?_
  induction n with
  | zero =>
    intro F _ _ f x _
    exact range_lTensor_le LinearMap.id _ (by simp) ⟨x, by simp⟩
  | succ k ih => exact relationsLift_succ J k hinj ih
end GlobalTheory.FibreFlatGen
