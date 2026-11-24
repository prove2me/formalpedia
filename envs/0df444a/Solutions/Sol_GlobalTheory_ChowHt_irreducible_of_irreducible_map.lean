-- Prove2me | solution 1 for GlobalTheory.ChowHt.irreducible_of_irreducible_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:17:31.111648+00:00
-- url     : https://prove2.me/submissions/38ad637f-eb8f-4cf8-a352-96e932ece43c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type} [Field k] {N : ℕ}
namespace GlobalTheory.ChowHt
theorem _root_.solution {K σ : Type} [Field K] [Algebra k K] {f : MvPolynomial σ k}
    (h : Irreducible (MvPolynomial.map (algebraMap k K) f)) : Irreducible f := by
  have key : ∀ a : MvPolynomial σ k, IsUnit (MvPolynomial.map (algebraMap k K) a) → IsUnit a := by
    intro a ha
    obtain ⟨c, hc, hca⟩ := isUnit_iff_eq_C_of_isReduced.1 ha
    have h0 : algebraMap k K (coeff 0 a) = c := by
      have := congrArg (coeff 0) hca
      rwa [coeff_map, coeff_zero_C] at this
    have ha' : a = C (coeff 0 a) := by
      apply map_injective (algebraMap k K) (algebraMap k K).injective
      rw [map_C, h0, hca]
    rw [ha']
    refine (IsUnit.mk0 _ fun h => hc.ne_zero ?_).map C
    rw [← h0, h, map_zero]
  refine ⟨fun hu => h.not_isUnit (hu.map _), fun a b hab => ?_⟩
  rw [hab, map_mul] at h
  exact (h.isUnit_or_isUnit rfl).imp (key a) (key b)
end GlobalTheory.ChowHt
