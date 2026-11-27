-- Prove2me | solution 1 for GlobalTheory.existsUnique_idele_of_linearEquiv_quotient_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:46.460786+00:00
-- url     : https://prove2.me/submissions/614cc480-3d1d-46d6-98a3-49aba2660df2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_Idele_mem_localIdeal_one_iff
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_mulEquiv_mk_eq_mk_iff
import Theorems.Thm_GlobalTheory_existsUnique_idele_of_linearEquiv_quotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk

set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors IsDedekindDomain.FiniteAdeleRing
noncomputable section
open GlobalTheory
open NumberField GlobalTheory.Idele
namespace GlobalTheory
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
    (φ : (K ⧸ ((1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) →ₗ[𝓞 K]
      (K ⧸ (𝔞 : Submodule (𝓞 K) K))) (hφ : Function.Bijective φ) :
    ∃! t : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (∀ x : K, x ∈ 𝔞 ↔ ∀ v, (t : FiniteAdeleRing (𝓞 K) K) v * algebraMap K (v.adicCompletion K) x
        ∈ v.adicCompletionIntegers K) ∧
      ∀ x y : K, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
        ∀ v, ((t⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v *
          algebraMap K (v.adicCompletion K) x - algebraMap K (v.adicCompletion K) y ∈
            localIdeal v 𝔞 := by
  have h1 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := one_ne_zero
  have key : ∀ (t : (FiniteAdeleRing (𝓞 K) K)ˣ) (x : K),
      x ∈ t⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
        ∀ v, (t : FiniteAdeleRing (𝓞 K) K) v * algebraMap K (v.adicCompletion K) x
          ∈ v.adicCompletionIntegers K := by
    intro t x
    rw [← algebraMap_mem_adelicIdeal (Idele.smul_ne_zero _ h1), ← mul_mem_adelicIdeal_smul t,
      smul_inv_smul, mem_adelicIdeal]
    simp_rw [mem_localIdeal_one_iff]
    rfl
  obtain ⟨t, ⟨h, ht⟩, huniq⟩ := existsUnique_idele_of_linearEquiv_quotient 𝔞 φ hφ
  refine ⟨t, ⟨fun x => by rw [← key, ← h], fun x y => by rw [ht, mulEquiv_mk_eq_mk_iff]⟩, ?_⟩
  rintro s ⟨hs, hs'⟩
  have h' : 𝔞 = s⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    ext x; rw [hs, key]
  refine huniq s ⟨h', fun q => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk x))
  rw [← hy, eq_comm, mulEquiv_mk_eq_mk_iff]
  exact (hs' x y).1 hy.symm
end GlobalTheory
