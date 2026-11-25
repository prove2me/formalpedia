-- Prove2me | solution 1 for GlobalTheory.GenSep.exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:20:26.922568+00:00
-- url     : https://prove2.me/submissions/d5b575c0-c978-4510-b151-a20fb2ee27ab

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
theorem _root_.solution (c : la.adicCompletion K) (ϖ : la.adicCompletionIntegers K) (hϖ : ϖ ≠ 0) :
    ∃ (a : K) (o : la.adicCompletionIntegers K),
      c - algebraMap K (la.adicCompletion K) a = (ϖ : la.adicCompletion K) * o := by
  have hϖ' : (ϖ : la.adicCompletion K) ≠ 0 := fun h => hϖ (Subtype.ext h)
  have hU : IsOpen {z : la.adicCompletion K | (c - z) * (ϖ : la.adicCompletion K)⁻¹ ∈ la.adicCompletionIntegers K} :=
    (Valued.isOpen_valuationSubring (la.adicCompletion K)).preimage ((continuous_const.sub continuous_id).mul continuous_const)
  obtain ⟨a, ha⟩ := (HeightOneSpectrum.denseRange_algebraMap K la).exists_mem_open hU ⟨c, by simp⟩
  refine ⟨a, ⟨_, ha⟩, ?_⟩
  field_simp
end GlobalTheory.GenSep
