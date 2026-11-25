-- Prove2me | solution 1 for GlobalTheory.flat_of_flat_residueField_baseChange_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:11.814573+00:00
-- url     : https://prove2.me/submissions/5971879f-9da6-4b57-b576-8a588ce93c4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_flat_of_flat_reduction_dvr
import Theorems.Thm_GlobalTheory_ker_includeRight_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
variable {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
variable {T : Type*} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra T A] [Algebra T B] [IsLocalRing B] [IsLocalHom (algebraMap T B)] [Module.Flat T B]
namespace GlobalTheory
theorem _root_.solution (φ : A →ₐ[T] B)
    (h : (Algebra.TensorProduct.map (AlgHom.id T (ResidueField T)) φ :
      ResidueField T ⊗[T] A →+* ResidueField T ⊗[T] B).Flat) : (φ : A →+* B).Flat :=
  flat_of_flat_reduction_dvr φ
    (Algebra.TensorProduct.includeRight : A →ₐ[T] ResidueField T ⊗[T] A)
    (Algebra.TensorProduct.includeRight : B →ₐ[T] ResidueField T ⊗[T] B) _
    (Algebra.TensorProduct.includeRight_surjective _ residue_surjective)
    (Algebra.TensorProduct.includeRight_surjective _ residue_surjective)
    (ker_includeRight_quotient A (maximalIdeal T)) (ker_includeRight_quotient B (maximalIdeal T))
    (by ext a; simp) h
end GlobalTheory
