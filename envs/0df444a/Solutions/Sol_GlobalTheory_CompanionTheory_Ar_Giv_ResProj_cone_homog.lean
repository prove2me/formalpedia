-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Giv.ResProj.cone_homog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:33.968097+00:00
-- url     : https://prove2.me/submissions/7593e09d-8a7a-4861-9460-7bf42228313d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Giv
open GlobalTheory.CompanionTheory.Ar.Giv.ResProj
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
namespace GlobalTheory.CompanionTheory.Ar.Giv.ResProj
theorem _root_.solution {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    mConeMap y f = C (aeval y f) * ∏ k, X k ^ a k := by
  unfold mConeMap
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, ι k), (X i.1 : MvPolynomial K Ω) ^ d i) = ∏ k, X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, (X k : MvPolynomial K Ω) ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc, map_mul, map_prod, map_pow]
  rw [mul_assoc]
  congr 1
end GlobalTheory.CompanionTheory.Ar.Giv.ResProj
