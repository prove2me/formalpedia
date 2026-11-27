-- Prove2me | solution 2 for GlobalTheory.finite_gaussVal_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:38:02.956573+00:00
-- url     : https://prove2.me/submissions/5e7b7fac-9227-45d0-9fe4-5a999a354604

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_gaussVal_apply
import Theorems.Thm_GlobalTheory_gaussAddValFrac_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.gaussAddValFrac_algebraMap

set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial Module IsDedekindDomain
namespace GlobalTheory
theorem _root_.solution {O K σ : Type*} [CommRing O] [IsDedekindDomain O] [Field K]
    [Algebra O K] [IsFractionRing O K] {f : MvPolynomial σ K} (hf : f ≠ 0) :
    {p : HeightOneSpectrum O | gaussVal (p.valuation K) f ≠ 1}.Finite := by
  obtain ⟨m₀, hm₀⟩ := ne_zero_iff.mp hf
  refine ((f.support.finite_toSet.biUnion fun m _ =>
    HeightOneSpectrum.Support.finite O (coeff m f)).union
      (HeightOneSpectrum.Support.finite O (coeff m₀ f)⁻¹)).subset fun p hp => ?_
  by_contra h
  simp only [Set.mem_union, Set.mem_iUnion, HeightOneSpectrum.Support, Set.mem_setOf_eq, not_or,
    not_exists, not_lt, map_inv₀] at h
  refine hp (le_antisymm ?_ ?_)
  · rw [gaussVal_apply]
    exact Finset.sup_le fun m hm => h.1 m hm
  · refine le_trans ?_ (le_gaussVal _ f m₀)
    exact (inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hm₀))).mp h.2
end GlobalTheory
