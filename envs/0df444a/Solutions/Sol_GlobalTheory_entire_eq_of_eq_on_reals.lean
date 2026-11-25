-- Prove2me | solution 1 for GlobalTheory.entire_eq_of_eq_on_reals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:34:09.794038+00:00
-- url     : https://prove2.me/submissions/72620838-15d9-4280-affd-a88f676548fc

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CapelliEigenRealToComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (p q : ℂ → E) (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (h : ∀ y : ℝ, p y = q y) : p = q := by
  have hp' : AnalyticOnNhd ℂ p Set.univ := fun z _ => hp.analyticAt z
  have hq' : AnalyticOnNhd ℂ q Set.univ := fun z _ => hq.analyticAt z
  refine AnalyticOnNhd.eq_of_frequently_eq (z₀ := ((0 : ℝ) : ℂ)) hp' hq' ?_
  have ht : Filter.Tendsto (fun y : ℝ => (y : ℂ)) (nhdsWithin 0 {0}ᶜ)
      (nhdsWithin ((0 : ℝ) : ℂ) {((0 : ℝ) : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      intro h0
      exact hy (Complex.ofReal_injective h0)
  exact ht.frequently (Filter.Frequently.of_forall h)
end GlobalTheory
