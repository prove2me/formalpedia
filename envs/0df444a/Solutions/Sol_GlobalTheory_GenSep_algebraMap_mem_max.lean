-- Prove2me | solution 1 for GlobalTheory.GenSep.algebraMap_mem_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:23:46.014597+00:00
-- url     : https://prove2.me/submissions/7cb3dc8d-fa49-4bbd-8981-b680ad6a0787

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.GenSep
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {Ω : Type} [Field Ω] [Algebra K Ω]
  {D N : ℕ}
namespace GlobalTheory.GenSep
theorem _root_.solution (a : 𝓞 K) :
    algebraMap (𝓞 K) (la.adicCompletionIntegers K) a ∈ maximalIdeal (la.adicCompletionIntegers K) ↔
      a ∈ la.asIdeal := by
  rw [mem_maximalIdeal, mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
    HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_eq_one_iff_notMem, not_not]
end GlobalTheory.GenSep
