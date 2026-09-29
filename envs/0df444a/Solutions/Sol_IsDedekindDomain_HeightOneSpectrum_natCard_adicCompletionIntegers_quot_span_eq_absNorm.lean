-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.natCard_adicCompletionIntegers_quot_span_eq_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1d14f105-4dea-5b51-b95b-681bd23a6e2f

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_quot_span_eq_absNorm

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K)
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) :
    Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span ({ϖ} : Set (v.adicCompletionIntegers K))) =
      Ideal.absNorm v.asIdeal := by
  classical

  have hmax : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) =
      Ideal.span ({ϖ} : Set (v.adicCompletionIntegers K)) :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer K v hϖ

  have e : (𝓞 K ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v
  have e' : (v.adicCompletionIntegers K ⧸ Ideal.span ({ϖ} : Set (v.adicCompletionIntegers K))) ≃+*
      IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    Ideal.quotEquivOfEq hmax.symm
  rw [Nat.card_congr (e'.toEquiv.trans e.toEquiv.symm), Ideal.absNorm_apply, Submodule.cardQuot_apply]

end S_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_quot_span_eq_absNorm
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_quot_span_eq_absNorm (solution)
