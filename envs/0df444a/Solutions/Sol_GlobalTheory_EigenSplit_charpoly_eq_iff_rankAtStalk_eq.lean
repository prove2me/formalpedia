-- Prove2me | solution 1 for GlobalTheory.EigenSplit.charpoly_eq_iff_rankAtStalk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:45:21.212093+00:00
-- url     : https://prove2.me/submissions/b9cca4d1-244d-423f-96c6-5db0d76f1523

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_charpoly_eq_iff_finrank_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul

set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  {N : Type*} [AddCommGroup N] [Module R N]
  {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)
include h
namespace GlobalTheory.EigenSplit
theorem _root_.solution [Module.Free R N] [Module.Finite R N] (r : ι → ℕ) :
    (∀ a, (ρ a).charpoly = ∏ i, (X - C (σ i a)) ^ r i) ↔
      ∀ (p : PrimeSpectrum R) i, Module.rankAtStalk (eigenSub ρ (σ i)) p = r i := by
  have key : ∀ p : PrimeSpectrum R,
      (∀ a, (ρ a).charpoly.map (algebraMap R (Localization.AtPrime p.asIdeal)) =
        (∏ i, (X - C (σ i a)) ^ r i).map (algebraMap R (Localization.AtPrime p.asIdeal))) ↔
      ∀ i, Module.rankAtStalk (eigenSub ρ (σ i)) p = r i := by
    intro p
    have := charpoly_eq_iff_finrank_eq (h.map (algebraMap R (Localization.AtPrime p.asIdeal)))
      (baseChangeAction (Localization.AtPrime p.asIdeal) ρ) r
    simp only [baseChangeAction_apply, LinearMap.charpoly_baseChange,
      ← (eigenBaseChangeEquiv _ ρ h _).finrank_eq] at this
    simp only [Module.rankAtStalk_eq_finrank_tensorProduct, ← this]
    simp [Polynomial.map_prod]
  constructor
  · intro hr p
    exact (key p).1 fun a => by rw [hr]
  · intro hr a
    ext n
    refine Module.eq_of_localization_maximal (R := R) (fun P _ => Localization.AtPrime P)
      (fun P _ => Algebra.linearMap R (Localization.AtPrime P)) _ _ fun m hm => ?_
    have := congrArg (fun q => Polynomial.coeff q n) ((key ⟨m, hm.isPrime⟩).2 (hr _) a)
    simp only [Polynomial.coeff_map] at this
    exact this
end GlobalTheory.EigenSplit
