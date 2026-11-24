-- Prove2me | solution 1 for GlobalTheory.Jet.polyDeriv_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:21:11.167339+00:00
-- url     : https://prove2.me/submissions/e5c2f44a-f4b3-46e3-ad37-21d64c92ad81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.Jet
variable {σ W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup W'] [NormedSpace ℂ W']
namespace GlobalTheory.Jet
theorem _root_.solution (P : MvPolynomial σ ℂ) (u : σ → W) (F : W' → ℂ) (φ : W ≃L[ℂ] W')
    (x : W) : polyDeriv P u (F ∘ φ) x = polyDeriv P (φ ∘ u) F (φ x) := by
  unfold polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := φ.iteratedFDerivWithin_comp_right F uniqueDiffOn_univ (Set.mem_univ (φ x))
    (Multiset.card (Finsupp.toMultiset m))
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  rw [h]
  rfl
end GlobalTheory.Jet
