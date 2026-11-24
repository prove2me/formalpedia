-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.Model.exists_finite_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:03.38711+00:00
-- url     : https://prove2.me/submissions/042aa766-122c-4c3d-9ff7-2f660c9a7daf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_NegOneNotSqSqrtTwo
import Theorems.Thm_GlobalTheory_QuadSymbol_Model_isQuadratic
import Theorems.Thm_GlobalTheory_QuadSymbol_Model_numberField
import Theorems.Thm_GlobalTheory_QuadSymbol_Model_eta_real_place

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory.QuadSymbol
open GlobalTheory GlobalTheory.QuadSymbol GlobalTheory.QuadSymbol.Model
variable {K : Type} [Field K] [Fact (∀ r : K, r ^ 2 ≠ -1 + 0 * r)]
namespace GlobalTheory.QuadSymbol.Model
theorem _root_.solution [NumberField K] (w : InfinitePlace K) (hw : w.IsReal)
    (hu : ∀ w', w' = w) (H : GlobalTheory.Published.QuadraticClassFieldTheory) :
    ∃ v : HeightOneSpectrum (𝓞 K),
      eta K (QuadraticAlgebra K (-1) 0) (v.adicCompletion K) (finDiag K (-1) v) = -1 := by
  have := isQuadratic (-1 : K)
  have := numberField (-1 : K)
  have h := ((H.1 K (QuadraticAlgebra K (-1) 0)).2.2.2 (-1)).2
  by_contra hn
  push Not at hn
  have h1 : ∀ v : HeightOneSpectrum (𝓞 K),
      eta K (QuadraticAlgebra K (-1) 0) (v.adicCompletion K) (finDiag K (-1) v) = 1 :=
    fun v => (Int.units_eq_one_or _).resolve_right (hn v)
  unfold etaProd at h
  rw [Finset.prod_eq_single w (fun b _ hb => absurd (hu b) hb) (by simp), eta_real_place w hw] at h
  simp only [h1, finprod_one, one_mul] at h
  exact absurd h (by decide)
end GlobalTheory.QuadSymbol.Model
