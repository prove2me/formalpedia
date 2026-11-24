-- Prove2me | solution 1 for GlobalTheory.existsUnique_idele_of_linearEquiv_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:11.833016+00:00
-- url     : https://prove2.me/submissions/410e09e2-cdd0-43b5-a572-1f16f8c2da03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_existsUnique_mulEquiv
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
    ∃! t : (FiniteAdeleRing (𝓞 K) K)ˣ, ∃ h : 𝔞 = t⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K),
      ∀ q, φ q = mulEquiv t⁻¹ one_ne_zero h q := by
  obtain ⟨t, ⟨h, ht⟩, huniq⟩ :=
    existsUnique_mulEquiv (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K)) (LinearEquiv.ofBijective φ hφ)
  refine ⟨t⁻¹, ?_, ?_⟩
  · simp only [inv_inv]
    exact ⟨h, fun q => LinearEquiv.congr_fun ht q⟩
  · rintro s ⟨h', hs⟩
    rw [← huniq s⁻¹ ⟨h', LinearEquiv.ext hs⟩, inv_inv]
end GlobalTheory
