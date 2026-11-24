-- Prove2me | solution 1 for GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:15:11.557938+00:00
-- url     : https://prove2.me/submissions/a301772f-5308-4abc-ac55-e38f25b27ef4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDualIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HermitianFormFiniteZerosOnLineCmExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinprodLocalDifferentIdealNormEqDiscr
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
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GlobalTheory.LocalDifferentProduct
namespace _root_.GlobalTheory.LocalDifferentProduct
theorem _root_.solution (x : 𝓞 K) :
    Valued.v ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) x : v.adicCompletionIntegers K) :
      v.adicCompletion K) = v.intValuation x := by
  simp [valuation_of_algebraMap]
end _root_.GlobalTheory.LocalDifferentProduct
end GlobalTheory.LocalDifferentProduct
