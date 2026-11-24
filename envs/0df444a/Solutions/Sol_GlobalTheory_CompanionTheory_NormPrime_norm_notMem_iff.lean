-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NormPrime.norm_notMem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:12:15.112922+00:00
-- url     : https://prove2.me/submissions/b085b133-7212-455c-bfca-e72dfff102ef

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_NormNotMemPrimeIff
import Theorems.Thm_GlobalTheory_CompanionTheory_NormPrime_norm_one_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_NormPrime_norm_mem_comap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NormPrime
open TensorProduct
namespace GlobalTheory.CompanionTheory.NormPrime
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] (e : B) (p : Ideal A) (hp : p.IsPrime) :
    Algebra.norm A e ∉ p ↔ ∀ q : Ideal B, q.IsPrime → q.comap (algebraMap A B) = p → e ∉ q := by
  constructor
  · intro hN q _ hc he
    exact hN (hc ▸ norm_mem_comap e q he)
  · intro H hN
    have h0 : Algebra.norm p.ResidueField ((1 : p.ResidueField) ⊗ₜ[A] e : p.ResidueField ⊗[A] B) = 0 := by
      rw [norm_one_tmul]
      exact (Ideal.algebraMap_residueField_eq_zero).2 hN
    have hnu : ¬ IsUnit ((1 : p.ResidueField) ⊗ₜ[A] e : p.ResidueField ⊗[A] B) := fun hu => by
      have := hu.map (Algebra.norm p.ResidueField)
      rw [h0] at this
      exact not_isUnit_zero this
    obtain ⟨m, hm, hem⟩ := exists_max_ideal_of_mem_nonunits hnu
    let f : B →ₐ[A] p.ResidueField ⊗[A] B := Algebra.TensorProduct.includeRight
    have hmp : m.IsPrime := hm.isPrime
    refine H (m.comap f) (Ideal.comap_isPrime f m) ?_ (Ideal.mem_comap.2 hem)
    ext a
    have hfa : f (algebraMap A B a) =
        algebraMap p.ResidueField (p.ResidueField ⊗[A] B) (algebraMap A p.ResidueField a) := by
      rw [f.commutes, IsScalarTower.algebraMap_apply A p.ResidueField]
    rw [Ideal.mem_comap, Ideal.mem_comap, hfa]
    constructor
    · intro ha
      by_contra hap
      have hne : algebraMap A p.ResidueField a ≠ 0 :=
        fun h => hap ((Ideal.algebraMap_residueField_eq_zero).1 h)
      exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ ha ((isUnit_iff_ne_zero.2 hne).map _))
    · intro ha
      rw [(Ideal.algebraMap_residueField_eq_zero).2 ha, map_zero]
      exact m.zero_mem
end GlobalTheory.CompanionTheory.NormPrime
