-- Prove2me | solution 1 for GlobalTheory.ringHom_flat_of_flat_quotientMap_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:00:51.313979+00:00
-- url     : https://prove2.me/submissions/dd4c60e1-b22a-410a-8813-dbafd795677e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_LocalFlat_flat_of_relationsLift
import Theorems.Thm_GlobalTheory_LocalFlat_relationsLift_of_square

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
namespace GlobalTheory
theorem _root_.solution (φ : A →+* B) {I : Ideal A} {J : Ideal B}
    (hIJ : I.map φ = J) (hJ : J ≤ Ideal.jacobson ⊥) (hle : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap φ)
    (h : ∀ n : ℕ, (Ideal.quotientMap (J ^ n) φ (hle n)).Flat) : φ.Flat := by
  letI := φ.toAlgebra
  refine LocalFlat.flat_of_relationsLift B (I := I) (hIJ.le.trans hJ) fun n => ?_
  refine LocalFlat.relationsLift_of_square (Ideal.Quotient.mk (I ^ n)) (Ideal.Quotient.mk (J ^ n))
    _ Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective Ideal.mk_ker ?_ ?_ (h n)
  · rw [Ideal.mk_ker, Ideal.map_pow, ← hIJ]
    rfl
  · exact Ideal.quotientMap_comp_mk (hle n)
end GlobalTheory
