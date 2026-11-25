-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.Model.exists_etaProd_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:06:22.33375+00:00
-- url     : https://prove2.me/submissions/9785404a-f86f-4fea-8c62-7e3077d5f756

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_NegOneNotSqSqrtTwo
import Theorems.Thm_GlobalTheory_QuadSymbol_Model_eta_real_place
import Theorems.Thm_GlobalTheory_QuadSymbol_eta_eq_one_iff


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
theorem _root_.solution [NumberField K] (w : InfinitePlace K) (hw : w.IsReal) :
    ∃ (x : FinFam K) (y : InfFam K), AlmostNorm K (QuadraticAlgebra K (-1) 0) x ∧
      etaProd K (QuadraticAlgebra K (-1) 0) x y = -1 := by
  classical
  refine ⟨1, Function.update 1 w (infDiag K (-1) w), ?_, ?_⟩
  · simp [AlmostNorm, one_mem]
  · have h1 : ∀ (A : Type) [CommRing A] [Algebra K A], eta K (QuadraticAlgebra K (-1) 0) A 1 = 1 :=
      fun A _ _ => eta_eq_one_iff.2 (one_mem _)
    unfold etaProd
    rw [Finset.prod_eq_single w]
    · simp [h1, eta_real_place w hw]
    · intro b _ hb
      rw [Function.update_of_ne hb]
      exact h1 _
    · simp
end GlobalTheory.QuadSymbol.Model
