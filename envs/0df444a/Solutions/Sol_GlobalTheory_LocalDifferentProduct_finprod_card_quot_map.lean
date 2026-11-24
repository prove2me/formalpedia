-- Prove2me | solution 1 for GlobalTheory.LocalDifferentProduct.finprod_card_quot_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:10:16.033572+00:00
-- url     : https://prove2.me/submissions/f843351d-d510-4151-a32d-168156186ee9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDualIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HermitianFormFiniteZerosOnLineCmExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinprodLocalDifferentIdealNormEqDiscr
import Theorems.Thm_GlobalTheory_LocalDifferentProduct_card_quot_map
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
open GlobalTheory GlobalTheory.LocalDifferentProduct
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial
namespace GlobalTheory.LocalDifferentProduct
namespace _root_.GlobalTheory.LocalDifferentProduct
theorem _root_.solution {K : Type} [Field K] [NumberField K] {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => Nat.card (v.adicCompletionIntegers K ⧸
      I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K)))).Finite ∧
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), Nat.card (v.adicCompletionIntegers K ⧸
      I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K))) = Ideal.absNorm I := by
  have hcard : ∀ v : HeightOneSpectrum (𝓞 K), Nat.card (v.adicCompletionIntegers K ⧸
      I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K))) = Ideal.absNorm (v.maxPowDividing I) :=
    fun v => _root_.GlobalTheory.LocalDifferentProduct.card_quot_map v hI
  simp_rw [hcard]
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => v.maxPowDividing I).Finite :=
    Ideal.finite_mulSupport hI
  refine ⟨hfin.subset (Function.mulSupport_comp_subset (map_one _) _), ?_⟩
  have h := MonoidHom.map_finprod (Ideal.absNorm : Ideal (𝓞 K) →*₀ ℕ).toMonoidHom hfin
  simp only [MonoidWithZeroHom.toMonoidHom_coe, Ideal.finprod_heightOneSpectrum_factorization hI] at h
  exact h.symm
end _root_.GlobalTheory.LocalDifferentProduct
end GlobalTheory.LocalDifferentProduct
