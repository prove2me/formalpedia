-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.blockFnField_joinPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:35:27.99873+00:00
-- url     : https://prove2.me/submissions/6d0a1aaa-530f-487f-a54a-8fa22681b84c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_HomogeneousFormNonvanishingPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SegreChart
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω] [CharZero Ω] {r : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.SegreChart
theorem _root_.solution (y : (Σ k, ι k) → Ω) (x' : Fin (r + 1) → Ω)
    (hF : ∀ i l, x' l ≠ 0 → x' i / x' l ∈ blockFnField y) :
    blockFnField (joinPt y x') = blockFnField y := by
  apply le_antisymm
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k | u, i⟩, ⟨k' | u', i'⟩, hpq, rfl⟩
    · obtain rfl : k = k' := Sum.inl.inj hpq
      exact IntermediateField.subset_adjoin _ _ ⟨⟨k, i⟩, ⟨k, i'⟩, rfl, rfl⟩
    · exact absurd hpq (by simp)
    · exact absurd hpq (by simp)
    · by_cases hl : x' i' = 0
      · change x' i / x' i' ∈ blockFnField y
        rw [hl, div_zero]
        exact zero_mem _
      · exact hF i i' hl
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin _ _
      ⟨joinInl _ _ p, joinInl _ _ q, by simp [joinInl, hpq], rfl⟩
end GlobalTheory.CompanionTheory.Ar.SegreChart
