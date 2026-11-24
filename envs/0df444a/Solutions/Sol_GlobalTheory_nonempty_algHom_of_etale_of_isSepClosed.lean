-- Prove2me | solution 1 for GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:24:58.25646+00:00
-- url     : https://prove2.me/submissions/a886ac01-3d78-4c93-a368-b4cada1bc9ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
variable {R A B K : Type*} [CommRing R] [CommRing A] [CommRing B] [Field K]
  [Algebra R A] [Algebra R B] [Algebra R K]
namespace GlobalTheory
theorem _root_.solution [IsSepClosed K] [Algebra.Etale R A] (q : Ideal A)
    [q.IsPrime] (hq : q.comap (algebraMap R A) = RingHom.ker (algebraMap R K)) :
    Nonempty (A →ₐ[R] K) := by
  let p := RingHom.ker (algebraMap R K)
  have : p.IsPrime := RingHom.ker_isPrime _
  have : q.LiesOver p := ⟨hq.symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver p q
  let ι : p.ResidueField →ₐ[R] K := Ideal.ResidueField.liftₐ p (Algebra.ofId R K) le_rfl (by
    simp [SetLike.le_def, IsUnit.mem_submonoid_iff, p])
  letI := ι.toAlgebra
  have : IsScalarTower R p.ResidueField K := .of_algebraMap_eq fun r => (ι.commutes r).symm
  let j : q.ResidueField →ₐ[p.ResidueField] K := IsSepClosed.lift
  exact ⟨(j.restrictScalars R).comp (IsScalarTower.toAlgHom R A _)⟩
end GlobalTheory
